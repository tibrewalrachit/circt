import Veda.Import.Netlist
import Veda.Import.Parser
import Std.Data.HashMap

/-!
# Elaboration: parsed generic ops → validated Circuit

Two passes over the parsed module:

1. Identify registers (`seq.firreg`, `seq.compreg`) and assign register
   indices; build the SSA symbol table (block args ↦ inputs, register
   results ↦ regs, other results ↦ nodes).
2. Elaborate the remaining ops into `CNode`s, then **topologically
   sort** them: `hw.module` bodies are MLIR *graph regions*, so textual
   order is not def-before-use (the counter references its register's
   fan-in before defining it). Register/input reads are sources; a
   combinational cycle is a hard error.

Unknown ops become `CNode.uninterp` (rule 2: total, honest import) —
the import *succeeds* and the ledger downgrades affected properties.
Structural failures (unparseable text, unsupported types, cycles,
multi-result ops we don't model) abort the import with an error.
-/

namespace Veda.Import

open Veda Std

/-- A node whose operand names still need resolving against the symbol
table. -/
private abbrev PreNode := (String → Except String CRef) → Except String CNode

/-- Width of the (single) result of an op. -/
private def resultWidth (op : GOp) : Except String Nat := do
  match op.resTypes with
  | [ty] => match typeWidth ty with
    | some w => pure w
    | none => throw s!"{op.name}: unsupported result type {ty}"
  | [] => pure 0
  | _ => throw s!"{op.name}: multi-result ops not yet supported"

private def argWidth (op : GOp) (i : Nat) : Except String Nat := do
  match op.argTypes[i]? >>= typeWidth with
  | some w => pure w
  | none => throw s!"{op.name}: cannot determine width of operand {i}"

private def oneOperand (op : GOp) (k : CRef → CNode) : PreNode :=
  fun res => do
    match op.operands with
    | [a] => pure (k (← res a))
    | _ => throw s!"{op.name}: expected 1 operand"

private def twoOperands (op : GOp) (k : CRef → CRef → CNode) : PreNode :=
  fun res => do
    match op.operands with
    | [a, b] => pure (k (← res a) (← res b))
    | _ => throw s!"{op.name}: expected 2 operands"

/-- Elaborate one non-register op into a deferred node builder. -/
private def elabOp (op : GOp) : Except String PreNode := do
  let w ← resultWidth op
  let variadic (vop : VarOp) : PreNode := fun res => do
    pure (.variadic vop w (← op.operands.mapM res))
  match op.name with
  | "hw.constant" =>
      match attrNat op.attrs "value" with
      | some v => pure fun _ => pure (.const w v)
      | none => throw s!"hw.constant: missing/unsupported value in `{op.attrs}`"
  | "comb.add" => pure (variadic .add)
  | "comb.mul" => pure (variadic .mul)
  | "comb.and" => pure (variadic .and)
  | "comb.or"  => pure (variadic .or)
  | "comb.xor" => pure (variadic .xor)
  | "comb.sub" => pure (twoOperands op (.sub w · ·))
  | "comb.mux" => pure fun res => do
      match op.operands with
      | [c, a, b] => pure (.mux w (← res c) (← res a) (← res b))
      | _ => throw "comb.mux: expected 3 operands"
  | "comb.icmp" => do
      let aw ← argWidth op 0
      match attrNat op.attrs "predicate" with
      | some p => pure (twoOperands op (.icmp p · · aw))
      | none => throw s!"comb.icmp: missing predicate in `{op.attrs}`"
  | "comb.extract" =>
      match attrNat op.attrs "lowBit" with
      | some lo => pure (oneOperand op (.extract w lo ·))
      | none => throw s!"comb.extract: missing lowBit in `{op.attrs}`"
  | "comb.concat" => do
      let widths ← (List.range op.operands.length).mapM (argWidth op)
      pure fun res => do
        pure (.concat w ((← op.operands.mapM res).zip widths))
  | "comb.replicate" => do
      let aw ← argWidth op 0
      pure (oneOperand op (.replicate w · aw))
  | "seq.to_clock" | "seq.from_clock" =>
      pure (oneOperand op (.clock ·))
  | other => pure fun res => do
      pure (.uninterp other w (← op.operands.mapM res))

/-- Is this op a register, and if so which operand is the next-value? -/
private def regNextOperand (op : GOp) : Option Nat :=
  match op.name with
  | "seq.firreg" => some 0   -- (next, clk[, reset, resetValue][, preset])
  | "seq.compreg" => some 0  -- (input, clk[, reset, resetValue][, powerOn])
  | _ => none

/-- Direct node→node dependencies. -/
private def nodeDeps (n : CNode) : List Nat :=
  let refs : List CRef := match n with
    | .const .. => []
    | .variadic _ _ args => args
    | .sub _ a b => [a, b]
    | .mux _ c a b => [c, a, b]
    | .icmp _ a b _ => [a, b]
    | .extract _ _ a => [a]
    | .concat _ args => args.map Prod.fst
    | .replicate _ a _ => [a]
    | .clock a => [a]
    | .uninterp _ _ args => args
  refs.filterMap fun r => match r with
    | .node i => some i
    | _ => none

private def remapNode (f : CRef → CRef) : CNode → CNode
  | .const w v => .const w v
  | .variadic op w args => .variadic op w (args.map f)
  | .sub w a b => .sub w (f a) (f b)
  | .mux w c a b => .mux w (f c) (f a) (f b)
  | .icmp p a b aw => .icmp p (f a) (f b) aw
  | .extract w lo a => .extract w lo (f a)
  | .concat w args => .concat w (args.map fun (r, rw) => (f r, rw))
  | .replicate w a aw => .replicate w (f a) aw
  | .clock a => .clock (f a)
  | .uninterp nm w args => .uninterp nm w (args.map f)

/-- Elaborate a parsed module into a validated circuit. -/
def elabModule (m : GModule) : Except String Circuit := do
  -- Input widths.
  let inputs ← m.inputs.mapM fun (n, ty) => do
    match typeWidth ty with
    | some w => pure (n, w)
    | none => throw s!"input {n}: unsupported type {ty}"
  -- Pass 1: symbol table.
  let mut table : HashMap String CRef := {}
  for (arg, idx) in m.blockArgs.zipIdx do
    table := table.insert arg (.input idx)
  let mut regsRaw : Array (String × Nat × String) := #[]
  let mut nodeOps : Array GOp := #[]
  for op in m.ops do
    match regNextOperand op with
    | some nextIdx =>
        let w ← match op.resTypes.head? >>= typeWidth with
          | some w => pure w
          | none => throw s!"{op.name}: bad register type"
        let nextName ← match op.operands[nextIdx]? with
          | some nm => pure nm
          | none => throw s!"{op.name}: missing next-value operand"
        let resName ← match op.results.head? with
          | some r => pure r
          | none => throw s!"{op.name}: register without result"
        table := table.insert resName (.reg regsRaw.size)
        regsRaw := regsRaw.push ((attrStr op.attrs "name").getD resName, w, nextName)
    | none =>
        match op.results with
        | [] => continue  -- result-less ops (e.g. verif.*) handled in M3
        | [r] =>
            table := table.insert r (.node nodeOps.size)
            nodeOps := nodeOps.push op
        | _ => throw s!"{op.name}: multi-result ops not yet supported"
  -- Pass 2: elaborate nodes at pre-topo indices.
  let tableF := table
  let resolve (name : String) : Except String CRef :=
    match tableF.get? name with
    | some r => pure r
    | none => throw s!"unknown SSA value {name}"
  let mut preNodes : Array CNode := #[]
  for op in nodeOps do
    let build ← elabOp op
    preNodes := preNodes.push (← build resolve)
  -- Topological sort (Kahn-style fixpoint).
  let n := preNodes.size
  let mut order : Array Nat := #[]
  let mut placed : Array Bool := (List.replicate n false).toArray
  let mut progress := true
  while order.size < n && progress do
    progress := false
    for i in List.range n do
      if !placed[i]! && (nodeDeps preNodes[i]!).all (fun j => placed[j]!) then
        order := order.push i
        placed := placed.set! i true
        progress := true
  if order.size < n then
    throw s!"combinational cycle among nodes in {m.name}"
  -- Remap node indices to topo positions.
  let posOf : HashMap Nat Nat :=
    order.toList.zipIdx.foldl (fun acc (old, new) => acc.insert old new) {}
  let remapRef (r : CRef) : CRef :=
    match r with
    | .node i => .node (posOf.get? i |>.getD i)
    | other => other
  let sortedNodes := order.toList.map fun i => remapNode remapRef preNodes[i]!
  -- Registers and outputs.
  let regsFinal ← regsRaw.toList.mapM fun (rname, w, nextName) => do
    pure { name := rname, width := w, next := remapRef (← resolve nextName) : Reg }
  let outWidths ← m.outputs.mapM fun (nm, ty) => do
    match typeWidth ty with
    | some w => pure w
    | none => throw s!"output {nm}: unsupported type {ty}"
  let outputs ← (m.outputOperands.zip outWidths).mapM fun (nm, w) => do
    pure (remapRef (← resolve nm), w)
  pure { name := m.name, inputs, regs := regsFinal, nodes := sortedNodes, outputs }

/-- End-to-end import: generic MLIR text → circuit. -/
def importCircuit (text : String) : Except String Circuit := do
  elabModule (← parseModule text)

end Veda.Import

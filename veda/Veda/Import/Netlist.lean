import Veda.Core.Design

/-!
# Netlist IR and its total interpreter

The importer's target: a `Circuit` is a validated, topologically sorted
netlist of `hw`/`comb`/`seq` operations. `Circuit.design` interprets it
as a `Veda.Design` whose state is the list of register values.

Totality and honesty (non-negotiable rule 2):

* Unknown MLIR ops become explicit `CNode.uninterp` nodes; their result
  is a fixed unknown-marker value. `Circuit.uninterpreted` lists them so
  the ledger can downgrade affected properties to `Assumed`.
* The elaborator validates widths and operand ordering
  (`Veda/Import/Elab.lean`); the interpreter itself is total, using
  width coercion as an unreachable-after-validation fallback (never a
  silent semantic choice — validation failure aborts the import).
* Registers (`seq.firreg`/`seq.compreg`) without power-on values leave
  the initial state unconstrained beyond its shape — `init` accepts
  *any* correctly-shaped register file, so theorems quantify over all
  power-on values.
-/

namespace Veda

/-- A width-annotated bitvector value. -/
def Val := Σ w : Nat, BitVec w

namespace Val

def mk (w : Nat) (v : BitVec w) : Val := ⟨w, v⟩

def ofNat (w n : Nat) : Val := ⟨w, BitVec.ofNat w n⟩

def width (v : Val) : Nat := v.1

/-- Coerce to a given width. After validation this is only ever applied
at the value's own width, where it reduces to the identity. -/
def castTo (w : Nat) : Val → BitVec w
  | ⟨w', v⟩ => if h : w' = w then h ▸ v else BitVec.ofNat w v.toNat

def beq : Val → Val → Bool
  | ⟨w1, v1⟩, ⟨w2, v2⟩ => if h : w1 = w2 then (h ▸ v1) == v2 else false

instance : BEq Val := ⟨beq⟩

instance : Repr Val := ⟨fun v _ => s!"{v.2.toNat}#{v.1}"⟩

end Val

/-- Reference to a value in the circuit: a module input, a register's
current value, or the result of an earlier node. -/
inductive CRef where
  | input (idx : Nat)
  | reg (idx : Nat)
  | node (idx : Nat)
  deriving Repr, DecidableEq

/-- Variadic combinational operators (`comb.add` etc. take N operands). -/
inductive VarOp where
  | add | mul | and | or | xor
  deriving Repr, DecidableEq

/-- Netlist node. Every node records its result width. `comb.icmp`
predicates use CIRCT's encoding (0=eq, 1=ne, 2=slt, 3=sle, 4=sgt,
5=sge, 6=ult, 7=ule, 8=ugt, 9=uge). -/
inductive CNode where
  | const (w : Nat) (val : Nat)
  | variadic (op : VarOp) (w : Nat) (args : List CRef)
  | sub (w : Nat) (a b : CRef)
  | mux (w : Nat) (c a b : CRef)
  | icmp (pred : Nat) (a b : CRef) (argWidth : Nat)
  | extract (w : Nat) (lowBit : Nat) (a : CRef)
  | concat (w : Nat) (args : List (CRef × Nat))
  | replicate (w : Nat) (a : CRef) (argWidth : Nat)
  /-- `seq.to_clock` and friends: clock plumbing, carried through as a
  1-bit value and never sampled (single-clock model, decision #9). -/
  | clock (a : CRef)
  /-- Explicit unknown op. Result is the all-zeros value of the result
  width; any property in its cone is `Assumed`, so this value is never
  load-bearing for a `Proven` verdict. -/
  | uninterp (name : String) (w : Nat) (args : List CRef)
  deriving Repr, Inhabited

/-- A register: current value is state; `next` is sampled at each tick. -/
structure Reg where
  name : String
  width : Nat
  next : CRef
  deriving Repr

/-- A flat, topologically sorted synchronous netlist. -/
structure Circuit where
  name : String
  inputs : List (String × Nat)
  regs : List Reg
  nodes : List CNode
  outputs : List (CRef × Nat)
  deriving Repr

namespace Circuit

/-- Names of uninterpreted ops present in the circuit (ledger feed). -/
def uninterpreted (c : Circuit) : List String :=
  c.nodes.filterMap fun n => match n with
    | .uninterp name _ _ => some name
    | _ => none

def evalRef (ins regs env : List Val) : CRef → Val
  | .input i => ins.getD i ⟨0, 0#0⟩
  | .reg i => regs.getD i ⟨0, 0#0⟩
  | .node i => env.getD i ⟨0, 0#0⟩

def evalVarOp (op : VarOp) (w : Nat) (args : List (BitVec w)) : BitVec w :=
  match op, args with
  | _, [] => 0#w
  | .add, a :: rest => rest.foldl (· + ·) a
  | .mul, a :: rest => rest.foldl (· * ·) a
  | .and, a :: rest => rest.foldl (· &&& ·) a
  | .or,  a :: rest => rest.foldl (· ||| ·) a
  | .xor, a :: rest => rest.foldl (· ^^^ ·) a

def evalIcmp (pred : Nat) {w : Nat} (a b : BitVec w) : Bool :=
  match pred with
  | 0 => a == b
  | 1 => a != b
  | 2 => a.slt b
  | 3 => a.sle b
  | 4 => b.slt a
  | 5 => b.sle a
  | 6 => a.ult b
  | 7 => a.ule b
  | 8 => b.ult a
  | 9 => b.ule a
  | _ => false

def evalNode (ins regs env : List Val) : CNode → Val
  | .const w v => Val.ofNat w v
  | .variadic op w args =>
      ⟨w, evalVarOp op w (args.map fun r => (evalRef ins regs env r).castTo w)⟩
  | .sub w a b =>
      ⟨w, (evalRef ins regs env a).castTo w - (evalRef ins regs env b).castTo w⟩
  | .mux w c a b =>
      if (evalRef ins regs env c).castTo 1 == 1#1 then
        ⟨w, (evalRef ins regs env a).castTo w⟩
      else
        ⟨w, (evalRef ins regs env b).castTo w⟩
  | .icmp pred a b aw =>
      ⟨1, if evalIcmp pred ((evalRef ins regs env a).castTo aw)
            ((evalRef ins regs env b).castTo aw) then 1#1 else 0#1⟩
  | .extract w lo a =>
      ⟨w, BitVec.extractLsb' lo w ((evalRef ins regs env a).2)⟩
  | .concat w args =>
      -- comb.concat: operands MSB-first; fold appends towards the LSB.
      let folded : Val := args.foldl
        (fun acc (r, rw) => ⟨acc.1 + rw, acc.2 ++ (evalRef ins regs env r).castTo rw⟩)
        ⟨0, 0#0⟩
      ⟨w, folded.castTo w⟩
  | .replicate w a aw =>
      let v := (evalRef ins regs env a).castTo aw
      ⟨w, (BitVec.replicate (w / max aw 1) v).setWidth w⟩
  | .clock a => ⟨1, (evalRef ins regs env a).castTo 1⟩
  | .uninterp _ w _ => ⟨w, 0#w⟩

/-- Evaluate all nodes in (topological) order. -/
def evalNodes (c : Circuit) (ins regs : List Val) : List Val :=
  c.nodes.foldl (fun env n => env ++ [evalNode ins regs env n]) []

/-- Next register file. -/
def stepFn (c : Circuit) (regs ins : List Val) : List Val :=
  let env := c.evalNodes ins regs
  c.regs.map fun r => ⟨r.width, (evalRef ins regs env r.next).castTo r.width⟩

/-- Current outputs. -/
def outFn (c : Circuit) (regs ins : List Val) : List Val :=
  let env := c.evalNodes ins regs
  c.outputs.map fun (r, w) => ⟨w, (evalRef ins regs env r).castTo w⟩

/-- The register file consisting of all zeros (a convenient concrete
initial state for simulation harnesses; the semantics does not
privilege it). -/
def zeroState (c : Circuit) : List Val :=
  c.regs.map fun r => ⟨r.width, 0#r.width⟩

/-- The imported design. State shape is constrained by `init`; register
power-on values are otherwise arbitrary (decision #2). -/
def design (c : Circuit) : Design where
  StateTy  := List Val
  InputTy  := List Val
  OutputTy := List Val
  init s   := s.map (·.1) = c.regs.map (·.width)
  step s i := c.stepFn s i
  out s i  := c.outFn s i

/-- `step` preserves the state shape, so `init`'s shape constraint is an
invariant of every valid trace. -/
theorem stepFn_shape (c : Circuit) (regs ins : List Val) :
    (c.stepFn regs ins).map (·.1) = c.regs.map (·.width) := by
  simp [stepFn]

end Circuit

end Veda

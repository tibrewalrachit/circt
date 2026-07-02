import Veda.Import.Elab
import Veda.Ltl.Semantics
import Std.Tactic.BVDecide

/-!
# The imported counter, and its first proved property

`counterCircuit` is the *transcribed* result of importing
designs/counter/counter.generic.mlir. Its authenticity is enforced twice:

* `counter_import_agrees` re-runs the importer on the embedded MLIR text
  at proof time (`native_decide` — reflection-trusted, reported by the
  axiom gate) and checks it produces exactly `counterCircuit`;
* the LSpec suite checks the embedded text is byte-identical to the file
  on disk, whose freshness against the pinned CIRCT release is in turn
  enforced by CI's import-roundtrip job.

So the chain designs/counter/counter.sv → circt-verilog → generic MLIR
→ importer → `counterCircuit` is closed, and `counter_wraps` below is a
theorem about the actual RTL modulo the documented TCB
(docs/architecture.md).

`counter_wraps` is the M2 milestone theorem: whenever the counter sits
at 255 with enable high and reset low, the *next* cycle reads 0 — stated
temporally via `holds` (`always (atMax |-> ##1 atZero)`) over all valid
traces and all register power-on values, proved from trace validity plus
a step-function characterization of the interpreter on the concrete
netlist. The proof is kernel-only (no compiled-code reflection); the
reflection-trusted `native_decide` is confined to the separate
importer-agreement theorem.
-/

namespace Veda.Designs

open Veda Veda.Import

/-- designs/counter/counter.generic.mlir, embedded. LSpec checks this
matches the file on disk. -/
def counterMlir : String :=
  r#"#loc = loc("counter.hw.mlir":2:67)
"builtin.module"() ({
  "hw.module"() <{module_type = !hw.modty<input clk : i1, input rst : i1, input en : i1, output count : i8>, parameters = [], result_locs = [#loc], sym_name = "counter"}> ({
  ^bb0(%arg0: i1, %arg1: i1, %arg2: i1):
    %0 = "hw.constant"() <{value = true}> : () -> i1
    %1 = "hw.constant"() <{value = 1 : i8}> : () -> i8
    %2 = "hw.constant"() <{value = 0 : i8}> : () -> i8
    %3 = "comb.add"(%10, %1) : (i8, i8) -> i8
    %4 = "comb.xor"(%arg1, %0) : (i1, i1) -> i1
    %5 = "comb.and"(%arg2, %4) : (i1, i1) -> i1
    %6 = "comb.mux"(%5, %3, %2) : (i1, i8, i8) -> i8
    %7 = "seq.to_clock"(%arg0) : (i1) -> !seq.clock
    %8 = "comb.or"(%arg1, %arg2) : (i1, i1) -> i1
    %9 = "comb.mux"(%8, %6, %10) <{twoState}> : (i1, i8, i8) -> i8
    %10 = "seq.firreg"(%9, %7) <{name = "count_q"}> : (i8, !seq.clock) -> i8
    "hw.output"(%10) : (i8) -> ()
  }) : () -> ()
}) : () -> ()
"#

/-- The imported circuit, transcribed from the importer's output. -/
def counterCircuit : Circuit where
  name := "counter"
  inputs := [("clk", 1), ("rst", 1), ("en", 1)]
  regs := [{ name := "count_q", width := 8, next := .node 9 }]
  nodes := [
    .const 1 1,                                   -- true
    .const 8 1,
    .const 8 0,
    .variadic .add 8 [.reg 0, .node 1],           -- count_q + 1
    .variadic .xor 1 [.input 1, .node 0],         -- !rst
    .variadic .and 1 [.input 2, .node 4],         -- en && !rst
    .mux 8 (.node 5) (.node 3) (.node 2),         -- en&&!rst ? q+1 : 0
    .clock (.input 0),
    .variadic .or 1 [.input 1, .input 2],         -- rst || en
    .mux 8 (.node 8) (.node 6) (.reg 0)]          -- rst||en ? _ : q
  outputs := [(.reg 0, 8)]

/-- The embedded MLIR imports to exactly `counterCircuit`. -/
theorem counter_import_agrees :
    (importCircuit counterMlir).toOption = some counterCircuit := by
  native_decide

namespace Counter

/-- The imported design. -/
abbrev D : Design := counterCircuit.design

def rstBit (i : List Val) : BitVec 1 := Val.castTo 1 (i[1]?.getD (⟨0, 0#0⟩ : Val))
def enBit (i : List Val) : BitVec 1 := Val.castTo 1 (i[2]?.getD (⟨0, 0#0⟩ : Val))

set_option linter.unusedSimpArgs false in
/-- Step-function characterization of the imported netlist: synchronous
reset dominates, enable increments, otherwise hold. Proved by unfolding
the interpreter on the concrete circuit (the input-bit case split is
kernel-`decide`d over the two 1-bit values). -/
theorem stepFn_spec (q : BitVec 8) (i : List Val) :
    counterCircuit.stepFn [⟨8, q⟩] i =
      [⟨8, if rstBit i = 1#1 then 0#8
           else if enBit i = 1#1 then q + 1#8 else q⟩] := by
  have hcast8 : ∀ v : BitVec 8, Val.castTo 8 ⟨8, v⟩ = v := fun _ => rfl
  have hcast1 : ∀ v : BitVec 1, Val.castTo 1 ⟨1, v⟩ = v := fun _ => rfl
  have hbit : ∀ x : BitVec 1, x = 1#1 ∨ x = 0#1 := by decide
  have h1 := hbit (rstBit i)
  have h2 := hbit (enBit i)
  simp only [rstBit] at h1
  simp only [enBit] at h2
  rcases h1 with hr | hr <;> rcases h2 with he | he <;>
    simp [counterCircuit, Circuit.stepFn, Circuit.evalNodes,
      Circuit.evalNode, Circuit.evalRef, Circuit.evalVarOp,
      Val.ofNat, hcast8, hcast1, rstBit, enBit, hr, he]

/-- Antecedent: counter at 255, enabled, not in reset. -/
def atMax (s i : List Val) : Bool :=
  s == [(⟨8, 255#8⟩ : Val)] && rstBit i == 0#1 && enBit i == 1#1

/-- Consequent: counter reads zero. -/
def atZero (s _i : List Val) : Bool := s == [(⟨8, 0#8⟩ : Val)]

/-- SVA reading: `always ((count==255 && en && !rst) |-> ##1 count==0)`. -/
def wrapProp : Prop' D :=
  .always (.imp (.atom atMax) (.seq (.delay (.atom atZero) 1 (some 0))))

/-- **M2 milestone theorem.** On every valid trace of the imported
counter — from every legal power-on value — whenever the count is 255
with enable high and reset low, the next cycle's count is 0. -/
theorem counter_wraps : holds D wrapProp := by
  intro t hv j _hj len hlen hm
  obtain ⟨hlen1, hant⟩ := hm
  subst hlen1
  simp only [atMax, Bool.and_eq_true, beq_iff_eq] at hant
  obtain ⟨⟨hs, hrst⟩, hen⟩ := hant
  -- Provide the ##1 match: total length 2, delay 1, atom length 1.
  refine ⟨2, 1, 1, ⟨Nat.le_refl 1, Nat.le_refl 1⟩, rfl, rfl, ?_⟩
  -- Next-cycle state via trace validity and the step characterization
  -- (`D.step` is `counterCircuit.stepFn` definitionally).
  have hstep : t.state (j + 1) = counterCircuit.stepFn (t.state j) (t.input j) :=
    hv.2 j
  simp only [atZero, beq_iff_eq]
  rw [Nat.add_sub_cancel, hstep, hs]
  -- Specialize the step characterization; the muxes reduce and the
  -- remaining leaf is 255 + 1 = 0 over BitVec 8.
  have hfin := stepFn_spec (255#8) (t.input j)
  rw [hrst, hen] at hfin
  simp at hfin
  exact hfin

end Counter

end Veda.Designs

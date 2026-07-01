import LSpec
import Veda
import Veda.Import.Elab

/-!
Import-pipeline tests: parse designs/counter/counter.generic.mlir,
elaborate to a `Circuit`, and check its interpreted behavior against a
hand-written Lean twin of counter.sv (synchronous reset dominates,
enable increments, 8-bit wrap). This is differential level 1
(Lean-vs-Lean); Verilator and arcilator legs land with the M2 harness.
-/

namespace Tests.Import

open Veda Veda.Import LSpec

/-- Hand-written twin of counter.sv: `if (rst) 0 else if (en) q+1`. -/
def twinStep (q : BitVec 8) (rst en : Bool) : BitVec 8 :=
  if rst then 0 else if en then q + 1 else q

/-- Inputs in module port order: clk, rst, en. -/
def mkIn (rst en : Bool) : List Val :=
  [⟨1, 1#1⟩, ⟨1, if rst then 1#1 else 0#1⟩, ⟨1, if en then 1#1 else 0#1⟩]

/-- Drive the imported circuit and the twin over the same stimulus,
comparing the register value at every step (starting from 0). -/
def agree (c : Circuit) (stim : List (Bool × Bool)) : Bool :=
  go c.zeroState 0 stim
where
  go (s : List Val) (q : BitVec 8) : List (Bool × Bool) → Bool
    | [] => true
    | (rst, en) :: rest =>
      let s' := c.stepFn s (mkIn rst en)
      let q' := twinStep q rst en
      s' == [(⟨8, q'⟩ : Val)] && go s' q' rest

/-- Deterministic pseudo-random stimulus (LCG), `n` steps. -/
def stimulus (n : Nat) (seed : Nat := 12345) : List (Bool × Bool) :=
  (List.range n).foldl
    (fun (acc : List (Bool × Bool) × Nat) _ =>
      let x := (acc.2 * 1103515245 + 12347) % 2147483648
      (acc.1 ++ [((x / 65536) % 4 == 0, (x / 131072) % 2 == 0)], x))
    ([], seed) |>.1

def suite (mlirText : String) : TestSeq :=
  match importCircuit mlirText with
  | .error e =>
      test s!"counter.generic.mlir imports (error: {e})" false
  | .ok c =>
      test "module name is counter" (c.name == "counter") $
      test "three 1-bit inputs" (c.inputs == [("clk", 1), ("rst", 1), ("en", 1)]) $
      test "one 8-bit register named count_q"
        (c.regs.map (fun r => (r.name, r.width)) == [("count_q", 8)]) $
      test "no uninterpreted ops" (c.uninterpreted == []) $
      test "output is the register value at reset-0 state"
        (c.outFn c.zeroState (mkIn false false) == [(⟨8, 0#8⟩ : Val)]) $
      test "imported circuit ≡ hand-written twin on 300 random steps"
        (agree c (stimulus 300)) $
      test "enable counts, disable holds, reset clears"
        (agree c [(false, true), (false, true), (false, false),
                  (true, true), (false, true)])

end Tests.Import

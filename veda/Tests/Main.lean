import LSpec
import Veda
import Tests.Ltl
import Tests.Import

/-!
LSpec sanity suites for the Veda core. These exercise the *executable*
side (simulation); the propositional side is covered by the theorems in
the library itself, which are checked by the axiom gate at build time.
-/

namespace Tests

open Veda LSpec

/-- An 8-bit wrapping counter with an enable input, the hand-written twin
of designs/counter/counter.sv. -/
def counter8 : Design where
  StateTy  := BitVec 8
  InputTy  := Bool           -- enable
  OutputTy := BitVec 8
  init s   := s = 0
  step s en := if en then s + 1 else s
  out s _  := s

def enabledSteps (n : Nat) : List Bool := List.replicate n true

/- `Design` fields are opaque to instance search; route decidability
through the underlying `BitVec 8`. -/
instance : DecidableEq counter8.OutputTy :=
  inferInstanceAs (DecidableEq (BitVec 8))

/-- State/output values with the right type ascription; `counter8.StateTy`
does not reduce for numeric literal elaboration. -/
def bv (n : Nat) : BitVec 8 := BitVec.ofNat 8 n

def suite : TestSeq :=
  test "counter counts when enabled"
    (counter8.simulate (bv 0) (enabledSteps 5) = [bv 0, bv 1, bv 2, bv 3, bv 4]) $
  test "counter holds when disabled"
    (counter8.simulate (bv 3) [false, false, true, false] = [bv 3, bv 3, bv 3, bv 4]) $
  test "counter wraps at 255"
    (counter8.simulate (bv 254) (enabledSteps 3) = [bv 254, bv 255, bv 0]) $
  test "simulate length matches input length"
    ((counter8.simulate (bv 0) (enabledSteps 100)).length = 100) $
  test "simulate on empty input is empty"
    (counter8.simulate (bv 0) [] = [])

end Tests

def main : IO UInt32 := do
  let counterMlir ← IO.FS.readFile "designs/counter/counter.generic.mlir"
  LSpec.lspecIO
    (.ofList [("Veda.Core", [Tests.suite]),
              ("Veda.Ltl", [Tests.Ltl.suite]),
              ("Veda.Import", [Tests.Import.suite counterMlir])]) []

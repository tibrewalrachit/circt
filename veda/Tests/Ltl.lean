import LSpec
import Veda

/-!
LSpec sanity suite for the ltl sequence evaluator. The design is a pure
"input probe": no state, the atoms observe the boolean input, so a trace
is just a list of booleans over time. Expected verdicts are hand-derived
from the SVA readings in docs/Dialects/LTL.md.
-/

namespace Tests.Ltl

open Veda LSpec

/-- Stateless design whose single input is a boolean signal. -/
def probe : Design where
  StateTy  := Unit
  InputTy  := Bool
  OutputTy := Unit
  init _   := True
  step _ _ := ()
  out _ _  := ()

/-- The input signal as an atom. -/
def sig : Seq probe := .atom fun _ b => b

/-- Finite trace from a boolean list. -/
def tr (bs : List Bool) : FinTrace probe := bs.map (((), ·))

-- `a ##1 a` — signal true at two consecutive ticks.
def twice : Seq probe := .concat sig (.delay sig 1 (some 0))

-- `##[1:3] a` — signal true 1 to 3 ticks from now.
def soon : Seq probe := .delay sig 1 (some 2)

-- `a[*2:3]` — two or three consecutive highs.
def burst : Seq probe := .rep sig 2 (some 1)

def suite : TestSeq :=
  test "atom matches iff signal high (len 1)"
    (smatchB (tr [true, false]) sig 0 1 = true &&
     smatchB (tr [true, false]) sig 1 1 = false) $
  test "atom never matches beyond trace end"
    (smatchB (tr [true]) sig 5 1 = false) $
  test "fusion of booleans is conjunction"
    (smatchB (tr [true]) (Seq.concat sig sig) 0 1 = true &&
     smatchB (tr [false]) (Seq.concat sig sig) 0 1 = false) $
  test "a ##1 a over [T,T] matches with len 2"
    (smatchB (tr [true, true]) twice 0 2 = true) $
  test "a ##1 a over [T,F] has no match"
    (smatchAnyB (tr [true, false]) twice 0 4 = false) $
  test "##[1:3] a hits a high at tick 2 (len 3)"
    (smatchB (tr [false, false, true]) soon 0 3 = true) $
  test "##[1:3] a misses when the high is too late"
    (smatchAnyB (tr [false, false, false, false, true]) soon 0 3 = false) $
  test "unbounded ##[1:$] a reaches a distant high"
    (smatchB (tr [false, false, false, false, true])
      (Seq.delay sig 1 none) 0 5 = true) $
  test "a[*2:3] matches two consecutive highs"
    (smatchB (tr [true, true, false]) burst 0 2 = true) $
  test "a[*2:3] matches three consecutive highs"
    (smatchB (tr [true, true, true]) burst 0 3 = true) $
  test "a[*2:3] rejects a single high"
    (smatchAnyB (tr [true, false, false]) burst 0 3 = false) $
  test "a[*0] has an empty match"
    (smatchB (tr [false]) (Seq.rep sig 0 (some 0)) 0 0 = true) $
  test "intersect demands equal-length matches"
    (smatchB (tr [true, true]) (Seq.intersect twice (.rep sig 2 (some 0))) 0 2 = true) $
  test "or matches through either branch"
    (smatchB (tr [false, true]) (Seq.or sig soon) 0 2 = true)

end Tests.Ltl

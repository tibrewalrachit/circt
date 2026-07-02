import Veda.Ltl.Semantics

/-!
# Bounded executable sequence matching

`SMatch` is a `Prop` with unbounded existentials, so it cannot be
executed directly. `smatchB` is its executable twin over a *finite*
trace (a list of state/input pairs): all quantifiers become bounded
searches, exploiting that a match of length `len` bounds every
component length by `len` and the repetition count by `n + len`.

Used by the LSpec suites and, later, for replaying `Disproven`
counterexample traces through the Lean semantics. Formal agreement
lemmas (`smatchB = true ↔ SMatch` on the embedded trace) are planned
alongside the M3 BMC cross-check; until then the evaluator is a test
oracle only, never cited as proof (it would fail the honesty rules
otherwise).
-/

namespace Veda

variable {D : Design}

/-- A finite trace: state and input at ticks `0..length-1`. -/
abbrev FinTrace (D : Design) := List (D.StateTy × D.InputTy)

/-- Executable window check. -/
def inWindowB (n : Nat) (w : Option Nat) (d : Nat) : Bool :=
  n ≤ d && match w with
    | none => true
    | some wnd => d ≤ n + wnd

/-- Executable `RepMatch`: `k` back-to-back matches via evaluator `M`. -/
def repMatchB (M : Nat → Nat → Bool) : Nat → Nat → Nat → Bool
  | 0, _, len => len == 0
  | k + 1, i, len =>
      (List.range (len + 1)).any fun l₁ =>
        M i l₁ && repMatchB M k (i + l₁) (len - l₁)

/-- Executable tight match on a finite trace. Atoms beyond the end of the
trace do not match. -/
def smatchB (t : FinTrace D) : Seq D → Nat → Nat → Bool
  | .atom f, i, len =>
      len == 1 && match t[i]? with
        | some (s, inp) => f s inp
        | none => false
  | .delay s n w, i, len =>
      (List.range (len + 1)).any fun d =>
        inWindowB n w d && smatchB t s (i + d) (len - d)
  | .concat a b, i, len =>
      (List.range (len + 1)).any fun la =>
        1 ≤ la && la ≤ len && smatchB t a i la &&
          smatchB t b (i + la - 1) (len + 1 - la)
  | .or a b, i, len => smatchB t a i len || smatchB t b i len
  | .and a b, i, len =>
      (smatchB t a i len && (List.range (len + 1)).any (smatchB t b i ·)) ||
      (smatchB t b i len && (List.range (len + 1)).any (smatchB t a i ·))
  | .intersect a b, i, len => smatchB t a i len && smatchB t b i len
  | .rep s n w, i, len =>
      let kmax := match w with
        | none => n + len
        | some wnd => min (n + wnd) (n + len)
      (List.range (kmax + 1)).any fun k =>
        inWindowB n w k && repMatchB (fun j l => smatchB t s j l) k i len

/-- Convenience: does the sequence match anywhere in the window
`[i, i+len]` of lengths `0..maxLen`? -/
def smatchAnyB (t : FinTrace D) (s : Seq D) (i maxLen : Nat) : Bool :=
  (List.range (maxLen + 1)).any (smatchB t s i ·)

end Veda

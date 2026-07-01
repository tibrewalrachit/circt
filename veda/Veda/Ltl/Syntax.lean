import Veda.Core.Design

/-!
# Syntax of the CIRCT ltl fragment

Deep embedding of the `ltl` dialect's sequences and properties, mirroring
CIRCT's operations (docs/Dialects/LTL.md at the pinned checkout):

* `Seq` ↔ `!ltl.sequence`: regular expressions over time. `atom` covers
  `i1` operands (the `i1 <: sequence` subtyping); `delay`/`concat`/`rep`
  are `ltl.delay`/`ltl.concat`/`ltl.repeat` with the same
  (base, optional window) encoding of `##[N:M]`/`##[N:$]`.
* `Prop'` ↔ `!ltl.property`: `seq` is the `sequence <: property`
  coercion; `imp` is the *overlapping* `ltl.implication` (`|->`);
  `until'` is **weak** and `eventually` is **strong**, exactly as CIRCT
  documents. `always` covers SVA's implicit assert-at-every-tick and the
  explicit `always` operator (see docs/semantics-decisions.md #9).

Not yet modeled (deferred, see docs/log/0002.md): `ltl.goto_repeat`,
`ltl.non_consecutive_repeat`, and `ltl.clock` (single-clock designs make
it a no-op wrapper; the importer will check and discharge that).
-/

namespace Veda

/-- Sequences: boolean atoms composed with temporal regex operators.
Delay/repeat windows follow CIRCT's encoding: `(n, some w)` spans
`[n, n+w]`, `(n, none)` is unbounded-but-finite (`##[n:$]`). -/
inductive Seq (D : Design) where
  /-- A boolean signal sampled at one tick (`i1` used as a sequence). -/
  | atom (f : D.StateTy → D.InputTy → Bool)
  /-- `ltl.delay %s, n[, w]` — prefix cycle delay. -/
  | delay (s : Seq D) (n : Nat) (w : Option Nat)
  /-- `ltl.concat %a, %b` — `##0` fusion: `b` starts the cycle `a` ends. -/
  | concat (a b : Seq D)
  /-- `ltl.or` on sequences: either matches. -/
  | or (a b : Seq D)
  /-- `ltl.and` on sequences: both match from the same start (lengths may
  differ); the combined match is the longer one. -/
  | and (a b : Seq D)
  /-- `ltl.intersect`: both match with the same length. -/
  | intersect (a b : Seq D)
  /-- `ltl.repeat %s, n[, w]` — consecutive repetition (`s[*n:m]`),
  instances separated by `##1`. -/
  | rep (s : Seq D) (n : Nat) (w : Option Nat)

/-- Properties over sequences. -/
inductive Prop' (D : Design) where
  /-- A sequence used as a property (`sequence <: property`). Interpreted
  as *strong* match existence; see docs/semantics-decisions.md #8. -/
  | seq (s : Seq D)
  | not (p : Prop' D)
  | and (p q : Prop' D)
  | or (p q : Prop' D)
  /-- `ltl.implication %s, %p` — overlapping `|->`: whenever `s` matches,
  `p` holds from the tick the match *ends* on. -/
  | imp (s : Seq D) (p : Prop' D)
  /-- `ltl.until %p, %q` — **weak**: `p` holds at every tick strictly
  before the first tick `q` holds; if `q` never holds, `p` holds forever. -/
  | until' (p q : Prop' D)
  /-- `ltl.eventually %p` — **strong**: `p` must hold at some tick. -/
  | eventually (p : Prop' D)
  /-- SVA `always p` / the implicit outermost quantification of
  `assert property`. -/
  | always (p : Prop' D)

namespace Prop'

/-- The constantly-true property. -/
def tt {D : Design} : Prop' D := .seq (.atom fun _ _ => true)

/-- The constantly-false property. -/
def ff {D : Design} : Prop' D := .seq (.atom fun _ _ => false)

end Prop'

end Veda

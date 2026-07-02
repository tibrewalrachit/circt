/-!
# Property ledger

Every imported property gets exactly one status in the ledger. The rules
(docs/architecture.md, "Non-negotiable rules"):

* `proven` may only be claimed for a kernel-checked theorem whose axioms
  pass the axiom gate.
* Any property whose cone of influence touches an `Uninterpreted` node is
  automatically downgraded to `assumed` — never silently approximated.
* A `disproven` verdict must carry a counterexample trace that replays
  through the Lean executable semantics, not just through an external
  tool.
-/

namespace Veda

/-- Verification status of a single imported property. The payloads are
placeholders until the importer (M2) fixes the trace representation. -/
inductive Status where
  /-- Kernel-checked theorem, standard axioms only, for all time and all
  parameters in scope. -/
  | proven
  /-- Refuted by a finite counterexample trace, replayed through
  `Design.simulate`. The payload records the trace provenance. -/
  | disproven (witness : String)
  /-- Only established up to `depth` clock cycles (e.g. via BMC
  cross-check); not a proof. -/
  | bounded (depth : Nat)
  /-- Taken on trust, with the reason recorded (e.g. cone of influence
  touches an `Uninterpreted` op). -/
  | assumed (reason : String)
  deriving Repr, DecidableEq

namespace Status

/-- Only `proven` counts as verified; everything else is an obligation. -/
def isVerified : Status → Bool
  | proven => true
  | _ => false

@[simp] theorem isVerified_proven : isVerified proven = true := rfl

@[simp] theorem isVerified_assumed (r : String) :
    isVerified (assumed r) = false := rfl

end Status

end Veda

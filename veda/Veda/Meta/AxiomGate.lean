import Lean

/-!
# Axiom gate

`#axiom_gate Veda` fails elaboration if any declaration under the given
namespace depends on axioms other than:

* the three standard Lean axioms (`propext`, `Classical.choice`,
  `Quot.sound`), and
* the compiler-reflection axioms introduced by `bv_decide`
  (`Lean.ofReduceBool` / per-theorem `<thm>._native.bv_decide.*`).

The reflection axioms are a deliberate, documented trust extension (see
docs/architecture.md, "Trust story"): `bv_decide` checks the SAT solver's
LRAT certificate with a *formally verified* checker, but executes that
checker via compiled native code rather than kernel reduction, so its
correctness rests on the Lean compiler in addition to the kernel. The gate
*reports* every declaration that relies on reflection so the exposure is
always visible in the build log; anything else — `sorryAx`, user-added
axioms — is a hard failure.

This runs at *build* time: CI builds `Tests/AxiomGate.lean`, which imports
the whole library and invokes the gate, so a red build is the enforcement
mechanism.
-/

namespace Veda.Meta

open Lean Elab Command

/-- The three standard axioms of Lean's kernel-checked core. -/
def allowedAxioms : List Name :=
  [``propext, ``Classical.choice, ``Quot.sound]

/-- Compiler-reflection axioms introduced by `bv_decide`'s native LRAT
certificate checking. Allowed but reported. -/
def isReflectionAxiom (n : Name) : Bool :=
  n == `Lean.ofReduceBool || n == `Lean.ofReduceNat ||
    n.components.contains (Name.mkSimple "_native")

elab "#axiom_gate " ns:ident : command => do
  let env ← getEnv
  let prefixName := ns.getId
  let mut checked := 0
  let mut reflective : Array Name := #[]
  let mut offenders : Array (Name × Array Name) := #[]
  for (name, _) in env.constants.toList do
    unless prefixName.isPrefixOf name do continue
    -- Skip compiler-generated auxiliary declarations.
    if name.isInternal then continue
    let axioms ← liftCoreM <| collectAxioms name
    checked := checked + 1
    if axioms.any isReflectionAxiom then
      reflective := reflective.push name
    let bad := axioms.filter fun a =>
      !allowedAxioms.contains a && !isReflectionAxiom a
    unless bad.isEmpty do
      offenders := offenders.push (name, bad)
  unless reflective.isEmpty do
    let msgs := reflective.toList.map (m!"  {·}")
    logInfo m!"axiom gate: {reflective.size} declaration(s) trust compiled-code reflection (bv_decide LRAT checking):\n{MessageData.joinSep msgs "\n"}"
  if offenders.isEmpty then
    logInfo m!"axiom gate: {checked} declarations under `{prefixName}` checked; only standard axioms (+ reported reflection) in use"
  else
    let msgs := offenders.toList.map fun (n, bad) => m!"  {n} depends on {bad.toList}"
    throwError m!"axiom gate FAILED: {offenders.size} declaration(s) use nonstandard axioms:\n{MessageData.joinSep msgs "\n"}"

end Veda.Meta

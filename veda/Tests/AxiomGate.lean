import Veda
import Veda.Meta.AxiomGate

/-!
Build-time axiom gate over the whole `Veda` library. Building this file
(part of the default lake targets) fails if any declaration under the
`Veda` namespace depends on axioms beyond propext, Classical.choice,
Quot.sound — in particular `sorry` and user-added axioms.
-/

#axiom_gate Veda

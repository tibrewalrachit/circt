import Lake
open Lake DSL

package veda where
  -- Fail the build on any warning in our own code (e.g. `sorry`).
  leanOptions := #[⟨`warningAsError, true⟩]

/-- LSpec test framework, vendored (see vendor/LSpec/LSPEC_COMMIT for the
pinned upstream commit). The development sandbox cannot clone from GitHub,
so this is a path dependency rather than a git dependency. -/
require LSpec from "vendor" / "LSpec"

@[default_target]
lean_lib Veda

/-- Shared test-suite modules (imported by the `tests` executable). -/
lean_lib TestSuites where
  roots := #[`Tests.Ltl, `Tests.Import]

/-- LSpec test suites. -/
lean_exe tests where
  root := `Tests.Main

/-- Differential-harness driver (stimulus generation, Lean-side
simulation of imported designs, arcilator testbench emission). -/
lean_exe harness where
  root := `Harness.Main

/-- Axiom gate: importing this module runs `#axiom_gate` over every theorem
in the `Veda` namespace and fails elaboration if any theorem depends on
axioms beyond propext, Classical.choice, Quot.sound. Built as part of CI. -/
@[default_target]
lean_lib Gate where
  roots := #[`Tests.AxiomGate]

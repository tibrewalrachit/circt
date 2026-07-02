/-!
# Synchronous designs as Mealy machines

A `Design` is the Lean-side denotation of a CIRCT `hw.module` after the
`moore → hw/comb/seq` lowering: a set of registers (`StateTy`), module
inputs (`InputTy`), module outputs (`OutputTy`), a set of legal reset
states (`init`), a one-clock-tick transition function (`step`), and a
combinational output function (`out`).

Conventions (recorded in docs/semantics-decisions.md):
* Time is the sequence of active clock edges of the design's single clock
  domain; multi-clock designs are out of scope until further notice.
* `init` is a *predicate*, not a single state, so designs with partially
  undefined reset values are representable without approximation.
* `step s i` is the state *after* the clock edge at which the inputs were
  `i` and the state was `s`; `out s i` is observed *before* that edge
  (standard Mealy convention).
-/

namespace Veda

/-- A synchronous hardware design, modeled as a Mealy machine with a
predicate describing its legal initial (reset) states. -/
structure Design where
  /-- Product of all register values (typically `BitVec n` components). -/
  StateTy  : Type
  /-- Module inputs sampled at each clock tick. -/
  InputTy  : Type
  /-- Module outputs, a combinational function of state and inputs. -/
  OutputTy : Type
  /-- Legal reset states. -/
  init     : StateTy → Prop
  /-- One clock tick: next state from current state and current inputs. -/
  step     : StateTy → InputTy → StateTy
  /-- Combinational outputs from current state and current inputs. -/
  out      : StateTy → InputTy → OutputTy

namespace Design

variable (D : Design)

/-- The state reached after `n` steps from `s0` under input stream `ins`. -/
def run (s0 : D.StateTy) (ins : Nat → D.InputTy) : Nat → D.StateTy
  | 0     => s0
  | n + 1 => D.step (run s0 ins n) (ins n)

@[simp] theorem run_zero (s0 : D.StateTy) (ins : Nat → D.InputTy) :
    D.run s0 ins 0 = s0 := by
  simp only [run]

@[simp] theorem run_succ (s0 : D.StateTy) (ins : Nat → D.InputTy) (n : Nat) :
    D.run s0 ins (n + 1) = D.step (D.run s0 ins n) (ins n) := by
  simp only [run]

/-- Running one step and then `n` steps of the shifted input stream is the
same as running `n + 1` steps. -/
theorem run_shift (s0 : D.StateTy) (ins : Nat → D.InputTy) (n : Nat) :
    D.run (D.step s0 (ins 0)) (fun k => ins (k + 1)) n = D.run s0 ins (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih => simp only [run_succ, ih]

end Design

end Veda

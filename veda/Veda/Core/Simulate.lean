import Veda.Core.Trace

/-!
# Executable simulation

`Design.simulate` runs a design on a finite input list, producing the
output at every tick. This is the Lean leg of the three-way differential
harness (Lean executable semantics vs. arcilator vs. Verilator).

`simulate_getElem` ties the executable simulator back to the trace
semantics: the `n`-th simulated output is the output function applied to
the state after `n` steps of `Design.run`. Combined with
`Trace.valid_state_eq_run`, simulation results are evidence about the
*semantics*, not just about the simulator.
-/

namespace Veda

namespace Design

variable (D : Design)

/-- Outputs and final state after feeding `ins` from state `s0`. -/
def simulateFrom (s0 : D.StateTy) : List D.InputTy → List D.OutputTy × D.StateTy
  | []        => ([], s0)
  | i :: rest =>
    let (outs, sN) := simulateFrom (D.step s0 i) rest
    (D.out s0 i :: outs, sN)

/-- Outputs observed when feeding the input list `ins` from state `s0`. -/
def simulate (s0 : D.StateTy) (ins : List D.InputTy) : List D.OutputTy :=
  (D.simulateFrom s0 ins).1

@[simp] theorem simulate_nil (s0 : D.StateTy) : D.simulate s0 [] = [] := rfl

@[simp] theorem simulate_cons (s0 : D.StateTy) (i : D.InputTy)
    (rest : List D.InputTy) :
    D.simulate s0 (i :: rest) = D.out s0 i :: D.simulate (D.step s0 i) rest := by
  simp [simulate, simulateFrom]

@[simp] theorem simulate_length (s0 : D.StateTy) (ins : List D.InputTy) :
    (D.simulate s0 ins).length = ins.length := by
  induction ins generalizing s0 with
  | nil => rfl
  | cons i rest ih => simp [ih]

/-- The `n`-th simulated output agrees with the trace semantics. `ext` is
any infinite input stream that extends the finite input list `ins`. -/
theorem simulate_getElem (s0 : D.StateTy) (ins : List D.InputTy)
    (ext : Nat → D.InputTy) (hext : ∀ k, (hk : k < ins.length) → ext k = ins[k])
    (n : Nat) (hn : n < ins.length) :
    (D.simulate s0 ins)[n]'(by simpa using hn) = D.out (D.run s0 ext n) ins[n] := by
  induction ins generalizing s0 ext n with
  | nil => exact absurd hn (Nat.not_lt_zero n)
  | cons i rest ih =>
    match n with
    | 0 => simp
    | m + 1 =>
      have h0 : ext 0 = i := hext 0 (Nat.succ_pos _)
      have hm : m < rest.length := Nat.lt_of_succ_lt_succ hn
      have hshift : ∀ k, (hk : k < rest.length) → ext (k + 1) = rest[k] :=
        fun k hk => hext (k + 1) (Nat.succ_lt_succ hk)
      have ih' := ih (D.step s0 i) (fun k => ext (k + 1)) hshift m hm
      simp only [simulate_cons, List.getElem_cons_succ]
      rw [ih', ← h0, run_shift]

end Design

end Veda

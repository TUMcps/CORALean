module

public import StepOfTest.Alg.Operations.Run

/-! Not a satellite: every use of `step_half` here is rejected, whether in a statement, a proof
term or a tactic proof. Unfolding `run`, which reaches the step without naming it, is no use. -/

@[expose] public section

namespace StepOfTest

theorem run_unfold_ok : run 4 = 3 := by decide

/--
error: `StepOfTest.step_half` is a step of `run`; only its file `StepOfTest.Alg.Operations.Run` and that file's satellite theorem files may use it (#227)
-/
#guard_msgs in
theorem half_le (n : Nat) : step_half n ≤ n := Nat.div_le_self n 2

/--
error: `StepOfTest.step_half` is a step of `run`; only its file `StepOfTest.Alg.Operations.Run` and that file's satellite theorem files may use it (#227)
-/
#guard_msgs in
theorem run_eq (n : Nat) : run n = n / 2 + 1 := by
  rw [run, step_half]

/--
error: `StepOfTest.step_half` is a step of `run`; only its file `StepOfTest.Alg.Operations.Run` and that file's satellite theorem files may use it (#227)
-/
#guard_msgs in
def half' (n : Nat) : Nat := step_half n + 1

end StepOfTest

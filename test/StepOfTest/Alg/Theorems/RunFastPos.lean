module

public import StepOfTest.Alg.Operations.RunFast

/-! A satellite of `RunFast.lean` only (the longer stem wins): it may read `step_quarter`, not
`step_half`. -/

@[expose] public section

namespace StepOfTest

theorem runFast_pos (n : Nat) : 0 < runFast n := by
  simp only [runFast, step_quarter, run]
  omega

/--
error: `StepOfTest.step_half` is a step of `run`; only its file `StepOfTest.Alg.Operations.Run` and that file's satellite theorem files may use it (#227)
-/
#guard_msgs in
theorem runFast_half (n : Nat) : runFast n = n / 4 / 2 + 1 := by
  simp only [runFast, run, step_quarter, step_half]

end StepOfTest

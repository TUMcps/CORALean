module

public import StepOfTest.Alg.Operations.RunFast

/-! A satellite of `Run.lean`: it may read `step_half`, in a statement, a proof, `simp` and
`unfold`, and through `step_half.eq_1`. -/

@[expose] public section

namespace StepOfTest

theorem half_le (n : Nat) : step_half n ≤ n := Nat.div_le_self n 2

theorem run_pos (n : Nat) : 0 < run n := by
  unfold run
  simp only [step_half.eq_1]
  omega

end StepOfTest

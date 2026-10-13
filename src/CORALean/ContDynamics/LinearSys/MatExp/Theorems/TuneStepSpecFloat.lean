module

public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.StepTestSpecFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.TuneStepFloat

@[expose] public section

/-!
# The step `tuneStep` returns is admissible

Induction on the fuel: the search returns either the candidate it just tested, which passed
`stepTest` and so is admissible by `stepTest_spec`, or what the search on the halved candidate
returns. Both satisfy `StepAdmissible`, [1]'s step predicate, at `toReal ε`. Maximality of the
step is not claimed.

## References

* [1] M. Wetzlinger, N. Kochdumper and M. Althoff. "Adaptive parameter tuning
      for reachability analysis of linear systems". CDC, 2020, pp. 5145–5152.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix NormedSpace FloatOps SoundFloatArithmetic

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Whatever `tuneStep` returns is admissible for `ε`. -/
theorem MatExp.tuneStep_spec {A : Mat ℝ n n} {nrm ε : 𝕋} {η : ℕ} (hA : ‖A‖ ≤ toReal nrm) :
    ∀ (fuel : ℕ) (r₀ r : 𝕋), MatExp.tuneStep nrm ε η r₀ fuel = some r →
      Real.MatExp.StepAdmissible A η (toReal ε) (toReal r)
  | 0, _, _, h => by simp [MatExp.tuneStep] at h
  | k + 1, r₀, r, h => by
    rw [MatExp.tuneStep] at h
    by_cases ht : MatExp.stepTest nrm ε η r₀ = true
    · rw [if_pos ht, Option.some.injEq] at h
      exact h ▸ MatExp.stepTest_spec hA ht
    · rw [if_neg ht] at h
      exact MatExp.tuneStep_spec hA k (half r₀) r h

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

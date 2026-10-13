import CORALean.ContDynamics.LinearSys.MatExp.Theorems.TendstoExpRemainderBoundZero
import CORALean.ContDynamics.LinearSys.Operations.TimeIntervalStepCurvatureError
import CORALean.ContDynamics.LinearSys.Operations.TimePointStepRemainderError
import CORALean.Global.ErrorConvergesToZero

/-!
# `Prop. 3`: `ε_H` converges to zero

[1, Prop. 3]: eq. (21)'s widening term shrinks to nothing as the step does,
which is `Assumption 1`'s first half. Both pieces of
`timeIntervalStepCurvatureError` vanish continuously at `0` — the finite
curvature term from `exp`'s own continuity, the remainder term from
`tendsto_expRemainderBound_zero` — the same route `ExistsTimeIntervalStepErrorLt`
already takes for the combined `timeIntervalStepError`, read here at the
non-hull half alone.

## References

* [1] M. Wetzlinger, N. Kochdumper and M. Althoff. "Adaptive parameter tuning
      for reachability analysis of linear systems". CDC, 2020, pp. 5145–5152.
-/

-- Authors:       Claude Opus 5
-- Written:       18-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix Scalar NormedSpace Filter Topology

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 3]: `ε_H` in eq. (21) satisfies `Assumption 1`. -/
theorem LinearSys.errorConvergesToZero_timeIntervalStepCurvatureError (sys : LinearSys 𝕋 n)
    (η : ℕ) (X₀ : Zonotope (Vec ℝ n)) :
    ErrorConvergesToZero
      (fun r => sys.timeIntervalStepCurvatureError r η X₀) := by -- --- PROOF ---
  set A := toRealMat sys.A with hA
  set B := ∑ j, X₀.absBound j with hB
  have hfun : (fun r : ℝ => sys.timeIntervalStepCurvatureError r η X₀)
      = fun r : ℝ => 2 * B * (Real.exp (r * ‖A‖) - 1 - r * ‖A‖
          + MatExp.expRemainderBound (r • A) η) := by
    funext r
    rw [LinearSys.timeIntervalStepCurvatureError, ← hA, ← hB]
  have hE2 : Tendsto (fun r : ℝ => Real.exp (r * ‖A‖) - 1 - r * ‖A‖)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hc : Continuous fun r : ℝ => Real.exp (r * ‖A‖) - 1 - r * ‖A‖ :=
      ((Real.continuous_exp.comp (continuous_id.mul continuous_const)).sub
        continuous_const).sub (continuous_id.mul continuous_const)
    have h : Tendsto (fun r : ℝ => Real.exp (r * ‖A‖) - 1 - r * ‖A‖) (𝓝[>] (0 : ℝ))
        (𝓝 (Real.exp ((0:ℝ) * ‖A‖) - 1 - (0:ℝ) * ‖A‖)) :=
      (hc.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    simpa using h
  unfold ErrorConvergesToZero
  rw [hfun]
  simpa using (hE2.add (MatExp.tendsto_expRemainderBound_zero A η)).const_mul (2 * B)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

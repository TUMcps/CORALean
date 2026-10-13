import CORALean.ContDynamics.LinearSys.MatExp.Theorems.TendstoMulExpRemainderBoundZero
import CORALean.ContDynamics.LinearSys.Operations.TimeIntervalStepCurvatureError
import CORALean.ContDynamics.LinearSys.Operations.TimePointStepRemainderError
import CORALean.Global.ErrorConvergesToZero

/-!
# `Prop. 4`: `ε_P` converges to zero

[1, Prop. 4]: eq. (22)'s widening term shrinks to nothing as the step does,
which is `Assumption 1`'s second half. `timePointStepRemainderError` is
`2·(∑ⱼ absBound j)` times `inputRemainder`'s own radius, so this reads
`tendsto_mul_expRemainderBound_zero` at a constant multiple.

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

/-- [1, Prop. 4]: `ε_P` in eq. (22) satisfies `Assumption 1`. -/
theorem LinearSys.errorConvergesToZero_timePointStepRemainderError (sys : LinearSys 𝕋 n)
    (η : ℕ) (U : Zonotope (Vec ℝ n)) :
    ErrorConvergesToZero (fun r => sys.timePointStepRemainderError r η U) := by -- --- PROOF ---
  set A := toRealMat sys.A with hA
  set B := ∑ j, U.absBound j with hB
  have hfun : (fun r : ℝ => sys.timePointStepRemainderError r η U)
      = fun r : ℝ => 2 * B * (r * MatExp.expRemainderBound (r • A) η) := by
    funext r
    rw [LinearSys.timePointStepRemainderError, ← hA, ← hB]
  unfold ErrorConvergesToZero
  rw [hfun]
  simpa using (MatExp.tendsto_mul_expRemainderBound_zero A η).const_mul (2 * B)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

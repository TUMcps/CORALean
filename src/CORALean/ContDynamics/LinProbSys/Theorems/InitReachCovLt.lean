module

public import CORALean.ContDynamics.LinProbSys.Operations.InitReachCov
public import CORALean.ContDynamics.LinearSys.Theorems.NoiseCovarianceDiagonal

@[expose] public section

/-!
# `initReach`'s input covariance is below the true one for an unstable `A`

In `ℝ¹` with `A = C = 1` and `r = 1` the noise accumulated over a step has variance
`(e² - 1)/2 ≈ 3.19`, and CORA's `Sigma` is `(1 - e⁻²)/2 ≈ 0.43`: the probabilistic zonotope
`initReach` and `post` build from it is too narrow, so the sets are not enclosures of the law
of the process [1]. For a stable `A` the same formula is too wide.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* CORA's input covariance is below the true noise covariance

## References

* [1] `contDynamics/@linProbSys/private/priv_inputSolution.m`
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinProbSys.initReachCov_lt_noiseCovariance :
    LinProbSys.initReachCov (fun _ : Fin 1 => (1 : ℝ)) (1 : Mat ℝ 1 1) 1 0 0
      < noiseCovariance (diagonal fun _ : Fin 1 => 1) (1 : Mat ℝ 1 1) 1 0 0 := by -- --- PROOF ---
  -- both sides in closed form: `(1 - e^{-2})/2 < (e^2 - 1)/2`
  rw [noiseCovariance_diagonal _ _ _ _ _ (by norm_num)]
  simp only [LinProbSys.initReachCov, transpose_one, mul_one, one_apply_eq]
  have hmul : Real.exp 2 * Real.exp (-2) = 1 := by rw [← Real.exp_add]; norm_num
  have hgt : 1 < Real.exp 2 := Real.one_lt_exp_iff.2 (by norm_num)
  have hpos : 0 < Real.exp (-2) := Real.exp_pos _
  norm_num
  nlinarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

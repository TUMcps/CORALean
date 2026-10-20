module

public import CORALean.ContDynamics.LinearSys.Theorems.NoiseCovarianceDiagonal

@[expose] public section

/-!
# [1, Sec. II]'s closed form for `Σ*_s` is the one for `-A`

In `ℝ¹` with `λ = 1`, `C = 1` and `t = 1`, `Σ_s(1) = ∫₀¹ e^{2(1-τ)} dτ = (e² - 1)/2`, while the
printed `(1 - e^{-2})/2` is smaller by the factor `e^{-2}`. They agree only at `t = 0`.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* the printed closed form differs from the noise covariance in the scalar example

## References

* [1] M. Althoff, O. Stursberg and M. Buss. "Safety Assessment for Stochastic Linear Systems
      using Enclosing Hulls of Probability Density Functions". In Proc. of the European Control
      Conference (ECC), pp. 625-630, 2009.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

theorem noiseCovariance_printed_counterexample : -- --- CONCL ---
    noiseCovariance (diagonal fun _ : Fin 1 => (1 : ℝ)) (1 : Mat ℝ 1 1) 1 0 0
      ≠ ((1 : Mat ℝ 1 1) * (1 : Mat ℝ 1 1).transpose) 0 0 / (1 + 1)
        * (1 - Real.exp (-(1 + 1) * 1)) := by -- --- PROOF ---
  rw [noiseCovariance_diagonal _ _ _ _ _ (by norm_num)]
  simp only [transpose_one, mul_one, one_apply_eq]
  intro h
  -- `e² - 1 = 1 - e^{-2}` would force `e² = 1`
  have h2 : Real.exp 2 - 1 = 1 - Real.exp (-2) := by norm_num at h ⊢; linarith
  have hpos : 0 < Real.exp (-2) := Real.exp_pos _
  have hmul : Real.exp 2 * Real.exp (-2) = 1 := by rw [← Real.exp_add]; norm_num
  have hgt : 1 < Real.exp 2 := Real.one_lt_exp_iff.2 (by norm_num)
  nlinarith
end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

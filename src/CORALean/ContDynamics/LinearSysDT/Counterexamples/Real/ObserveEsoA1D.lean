module

public import CORALean.ContDynamics.LinearSysDT.Operations.ObserveEsoA1D
public import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

/-!
# CORA's observer `ESO-A` misses the true state

A run of `priv_observe_ESO_A` on `x_{k+1} = x_k + w_k`, `y_k = 2 x_k + v_k`, with `R0 = E(0, 10/3)`,
`W = E(0, 1/4)` and `V = E(0, 220²)` (`phi = 220`). The initial state `x₀ = 9/5` lies in `R0`; the
first measurement has `0.3 + δ² = 0.3 + 3.6² ≤ 220`, so the initial update does not fire. The
disturbance `w = 1/2` gives `x₁ = 23/10`, measured as `y₂ = 17` (`v = 12.4`). The step fires,
takes `λ = 1e-4` and returns the center `51/2000` and the shape `12500000/9713231`
(`sigma_sq ≈ 5.81`), which misses `x₁`: `(x₁ - c)² / Q ≈ 4.0 > 1`. The cause is the update's
division by `sigma_sq` (`Ellipsoid.intersectStripGollamudi1D_counterexample`). Read from the
source, not run.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* the true next state lies outside the estimate
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- `x₀ ∈ R0`, the first update does not fire, `w ∈ W`, `v ∈ V`, and `x₁` is not in the
estimate. -/
theorem LinearSysDT.observeEsoA1D_counterexample : -- --- CONCL ---
    let x₀ : ℝ := 9 / 5
    let w : ℝ := 1 / 2
    let x₁ : ℝ := 1 * x₀ + 0 + w
    let est := LinearSysDT.observeEsoA1D 1 2 (1 / 4) 48400 0 17 (10 / 3) 0 (3 / 10)
    x₀ ^ 2 / (10 / 3) ≤ 1 ∧ 3 / 10 + (2 * x₀ - 2 * 0) ^ 2 ≤ Real.sqrt 48400 ∧
      w ^ 2 / (1 / 4) ≤ 1 ∧ (17 - 2 * x₁) ^ 2 / 48400 ≤ 1 ∧
      1 < (x₁ - est.1) ^ 2 / est.2.1 := by -- --- PROOF ---
  intro x₀ w x₁ est
  have h220 : Real.sqrt 48400 = 220 := by norm_num
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · norm_num [x₀]
  · rw [h220]; norm_num [x₀]
  · norm_num [w]
  · norm_num [x₁, x₀, w]
  -- the step in closed form
  have hc : est.1 = 51 / 2000 := by
    simp only [est, LinearSysDT.observeEsoA1D, Ellipsoid.intersectStripGollamudi1D]
    norm_num
  have hq : est.2.1 = 12500000 / 9713231 := by
    simp only [est, LinearSysDT.observeEsoA1D, Ellipsoid.intersectStripGollamudi1D]
    norm_num
  rw [hc, hq]
  norm_num [x₁, x₀, w]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

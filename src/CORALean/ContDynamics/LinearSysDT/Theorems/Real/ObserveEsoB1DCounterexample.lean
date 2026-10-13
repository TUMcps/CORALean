import CORALean.ContDynamics.LinearSysDT.Operations.ObserveEsoB1D
import Mathlib.Tactic.NormNum.RealSqrt

/-!
# CORA's observer `ESO-B` misses the true state

A run of `priv_observe_ESO_B` on `x_{k+1} = x_k + w_k`, `y_k = x_k + v_k`, with
`R0 = E(0, 5/6)`, `W = E(0, 1/100)` and `V = E(0, 9)` (`bar_V = 1/3`). The initial state
`x₀ = -9/10` lies in `R0`; the first measurement `y₁ = 0` (`v = 9/10`) has `0.3 + δ² = 0.3 ≤ 1`,
so the initial update does not fire and the first estimate is `R0` with `sigma_sq = 0.3`. The
disturbance `w = -1/10` gives `x₁ = -1`, measured as `y₂ = 6/5` (`v = 11/5`). The step predicts
`p = 1/6`, `Q_next = 6/5`, fires (`0.3 + (6/5)² > 1`), takes `λ = 3/5` (`g = 2/15`,
`√(g/ω) = 12/25`) and returns the centre `1/5`, the shape `2/5` and `sigma_sq = 16/25`, which
misses `x₁`: `(x₁ - c)² / Q = 18/5 > 1`, and also as the level-`sigma_sq` set,
`(x₁ - c)² / (sigma_sq Q) = 45/8 > 1`. The cause is the update's shape, `(1 - λ)²` times the
one the fusion needs (`Ellipsoid.intersectStripLiu1D_counterexample`): at `(1 - λ)⁻²` times it,
`5/2`, the level-`sigma_sq` set has `(x₁ - c)² = 36/25 ≤ sigma_sq · 5/2 = 8/5` and holds `x₁`.
Read from the source, not run.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- `x₀ ∈ R0`, the first update does not fire, `v₁ ∈ V`, `w ∈ W`, `v₂ ∈ V`, and `x₁` is in
neither the estimate nor its level-`sigma_sq` set. -/
theorem LinearSysDT.observeEsoB1D_counterexample :
    let x₀ : ℝ := -9 / 10
    let w : ℝ := -1 / 10
    let x₁ : ℝ := 1 * x₀ + 0 + w
    let est := LinearSysDT.observeEsoB1D 1 1 (1 / 100) 9 0 (6 / 5) (5 / 6) 0 (3 / 10)
    x₀ ^ 2 / (5 / 6) ≤ 1 ∧ 3 / 10 + (0 - 1 * 0) ^ 2 ≤ (1 : ℝ) ∧ (0 - 1 * x₀) ^ 2 / 9 ≤ 1 ∧
      w ^ 2 / (1 / 100) ≤ 1 ∧ (6 / 5 - 1 * x₁) ^ 2 / 9 ≤ 1 ∧
      1 < (x₁ - est.1) ^ 2 / est.2.1 ∧
      1 < (x₁ - est.1) ^ 2 / (est.2.2 * est.2.1) := by -- --- PROOF ---
  intro x₀ w x₁ est
  refine ⟨?_, by norm_num, ?_, ?_, ?_, ?_⟩
  · norm_num [x₀]
  · norm_num [x₀]
  · norm_num [w]
  · norm_num [x₁, x₀, w]
  -- the step in closed form: `λ = 3/5`, `K = 1/6`
  have hc : est.1 = 1 / 5 := by
    simp only [est, LinearSysDT.observeEsoB1D, Ellipsoid.intersectStripLiu1D]
    norm_num
  have hq : est.2.1 = 2 / 5 := by
    simp only [est, LinearSysDT.observeEsoB1D, Ellipsoid.intersectStripLiu1D]
    norm_num
  have hs : est.2.2 = 16 / 25 := by
    simp only [est, LinearSysDT.observeEsoB1D, Ellipsoid.intersectStripLiu1D]
    norm_num
  rw [hc, hq, hs]
  norm_num [x₁, x₀, w]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

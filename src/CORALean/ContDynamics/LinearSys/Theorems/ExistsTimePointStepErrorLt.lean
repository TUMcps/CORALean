module

public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.TendstoMulExpRemainderBoundZero
public import CORALean.ContDynamics.LinearSys.Operations.TimePointStepError
public import CORALean.ContDynamics.LinearSys.Operations.TimeIntervalStepError

@[expose] public section

/-!
# Any admissible error is reachable, in the step's own error

The statement that makes "tune the parameters against an admissible error" true of the enclosure
rather than of a series remainder: for every `ε > 0` there is a step at which `timePointStepError`
is under `ε`, and whose side condition holds, so the `r` produced names a step
`timePointStep_subset_reach_add_error` applies at. The order is given rather than chosen. Both parts
of the error vanish with the step and only one of them with the order, so shrinking the step is what
answers for an arbitrary `ε`; a larger `η` buys a smaller remainder at a fixed step and never
touches the dependency term. That asymmetry is why [1] tunes the step size and not the order alone.

## Inputs
* `sys` – linear system
* `U` – input zonotope
* `η` – Taylor order
* `ε` – admissible error

## Hypotheses
* `hε` – error positive

## Conclusion
* some step has enclosure error under the error and meets the side condition

## References

* [1] M. Wetzlinger, N. Kochdumper and M. Althoff. "Adaptive parameter tuning for reachability
      analysis of linear systems". 2020 59th IEEE Conference on Decision and Control (CDC), 2020.
-/

-- Authors:       Claude Opus 5
-- Written:       08-September-2026
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

/-- A step whose whole enclosure error is under `ε`, sound because its own side
condition holds too. -/
theorem LinearSys.exists_timePointStepError_lt (sys : LinearSys 𝕋 n) (U : Zonotope (Vec ℝ n))
    (η : ℕ) {ε : ℝ} (hε : 0 < ε) : -- --- CONCL ---
    ∃ r : ℝ, 0 < r ∧ sys.timePointStepError r η U < ε ∧
      ‖r • toRealMat sys.A‖ / ((η : ℝ) + 2) < 1 := by -- --- PROOF ---
  set A := toRealMat sys.A with hA
  set B := ∑ j, U.absBound j with hB
  -- the error, split into the two terms that vanish for different reasons
  have hfun : (fun r : ℝ => sys.timePointStepError r η U)
      = fun r : ℝ => 2 * B * (r * (Real.exp (r * ‖A‖) - 1))
          + 2 * B * (r * MatExp.expRemainderBound (r • A) η) := by
    funext r
    rw [LinearSys.timePointStepError, ← hA, ← hB]
    ring
  have hcont : Continuous fun r : ℝ => 2 * B * (r * (Real.exp (r * ‖A‖) - 1)) :=
    continuous_const.mul (continuous_id.mul
      ((Real.continuous_exp.comp (continuous_id.mul continuous_const)).sub continuous_const))
  have h1 : Tendsto (fun r : ℝ => 2 * B * (r * (Real.exp (r * ‖A‖) - 1)))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h : Tendsto (fun r : ℝ => 2 * B * (r * (Real.exp (r * ‖A‖) - 1)))
        (𝓝[>] (0 : ℝ)) (𝓝 (2 * B * (0 * (Real.exp (0 * ‖A‖) - 1)))) :=
      (hcont.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    simpa using h
  have h2 : Tendsto (fun r : ℝ => 2 * B * (r * MatExp.expRemainderBound (r • A) η))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using (MatExp.tendsto_mul_expRemainderBound_zero A η).const_mul (2 * B)
  -- the side condition, which is what makes the step produced a sound one
  have hnorm : Tendsto (fun r : ℝ => ‖r • A‖) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have heq : (fun r : ℝ => ‖r • A‖) = fun r => |r| * ‖A‖ := by
      funext r
      rw [norm_smul, Real.norm_eq_abs]
    have h : Tendsto (fun r : ℝ => |r|) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa using (continuous_abs.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    rw [heq]
    simpa using h.mul_const ‖A‖
  have hT2 : Tendsto (fun r : ℝ => ‖r • A‖ / ((η : ℝ) + 2)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using hnorm.div_const ((η : ℝ) + 2)
  have hev1 : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), sys.timePointStepError r η U < ε := by
    have hsum : Tendsto (fun r : ℝ => sys.timePointStepError r η U)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      rw [hfun]
      simpa using h1.add h2
    exact hsum.eventually_lt_const hε
  -- a step meeting all three at once is what the filter's nonemptiness gives
  have hev2 : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), ‖r • A‖ / ((η : ℝ) + 2) < 1 :=
    hT2.eventually_lt_const one_pos
  have hev3 : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), (0 : ℝ) < r := self_mem_nhdsWithin
  obtain ⟨r, ⟨hr1, hr2⟩, hr3⟩ := ((hev1.and hev2).and hev3).exists
  exact ⟨r, hr3, hr1, hr2⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

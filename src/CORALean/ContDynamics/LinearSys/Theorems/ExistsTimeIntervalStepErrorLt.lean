module

public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.TendstoExpRemainderBoundZero
public import CORALean.ContDynamics.LinearSys.Operations.TimePointStepError
public import CORALean.ContDynamics.LinearSys.Operations.TimeIntervalStepError
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional

@[expose] public section

/-!
# Any admissible error is reachable, over the whole step

`ExistsTimePointStepErrorLt` at the time-interval step: for every `ε > 0` there is a step at which
`timeIntervalStepError` is under `ε`, and whose side condition holds, so the `r` produced names a
step `timeIntervalStep_subset_reach_add_error` applies at. The order does even less here than at the
step's end. Two of the three parts (the hull `‖e^{rA} - I‖` and the curvature `e^{r‖A‖} - 1 - r‖A‖`)
do not mention it at all, and the hull is first order in the step where everything else is second.
Shrinking the step is the only knob that answers for an arbitrary `ε`, which is what [1] tunes the
step size and not only the order for.

## Inputs
* `sys` – linear system
* `X₀` – initial zonotope
* `η` – Taylor order
* `ε` – admissible error

## Hypotheses
* `hε` – error positive

## Conclusion
* some step has enclosure error under the error and meets the side condition

## References

* [1] M. Wetzlinger, N. Kochdumper and M. Althoff. "Adaptive parameter tuning
      for reachability analysis of linear systems". CDC, 2020, pp. 5145–5152.
-/

-- Authors:       Claude Opus 5
-- Written:       08-September-2026
-- Last update:   ---
-- Reviewed:      15-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix Scalar NormedSpace Filter Topology

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

/-- A step whose whole time-interval enclosure error is under `ε`, sound because
its own side condition holds too. -/
theorem LinearSys.exists_timeIntervalStepError_lt (sys : LinearSys 𝕋 n)
    (X₀ : Zonotope (Vec ℝ n)) (η : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ sys.timeIntervalStepError r η X₀ < ε ∧
      ‖r • toRealMat sys.A‖ / ((η : ℝ) + 2) < 1 := by -- --- PROOF ---
  set A := toRealMat sys.A with hA
  set B := ∑ j, X₀.absBound j with hB
  have hfun : (fun r : ℝ => sys.timeIntervalStepError r η X₀)
      = fun r : ℝ => B * (‖exp (r • A) - 1‖
          + 2 * (Real.exp (r * ‖A‖) - 1 - r * ‖A‖
            + MatExp.expRemainderBound (r • A) η)) := by
    funext r
    rw [LinearSys.timeIntervalStepError, ← hA, ← hB]
  -- the hull term, which is where the exponential's own continuity is used
  have hE1 : Tendsto (fun r : ℝ => ‖exp (r • A) - 1‖) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hc : Continuous fun r : ℝ => ‖exp (r • A) - (1 : Mat ℝ n n)‖ :=
      ((NormedSpace.exp_continuous.comp (continuous_id.smul continuous_const)).sub
        continuous_const).norm
    have h : Tendsto (fun r : ℝ => ‖exp (r • A) - (1 : Mat ℝ n n)‖) (𝓝[>] (0 : ℝ))
        (𝓝 ‖exp ((0:ℝ) • A) - (1 : Mat ℝ n n)‖) :=
      (hc.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    simpa using h
  have hE2 : Tendsto (fun r : ℝ => Real.exp (r * ‖A‖) - 1 - r * ‖A‖)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hc : Continuous fun r : ℝ => Real.exp (r * ‖A‖) - 1 - r * ‖A‖ :=
      ((Real.continuous_exp.comp (continuous_id.mul continuous_const)).sub
        continuous_const).sub (continuous_id.mul continuous_const)
    have h : Tendsto (fun r : ℝ => Real.exp (r * ‖A‖) - 1 - r * ‖A‖) (𝓝[>] (0 : ℝ))
        (𝓝 (Real.exp ((0:ℝ) * ‖A‖) - 1 - (0:ℝ) * ‖A‖)) :=
      (hc.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    simpa using h
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
  have hev1 : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), sys.timeIntervalStepError r η X₀ < ε := by
    have hsum : Tendsto (fun r : ℝ => sys.timeIntervalStepError r η X₀)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      rw [hfun]
      simpa using
        ((hE1.add ((hE2.add (MatExp.tendsto_expRemainderBound_zero A η)).const_mul 2)).const_mul B)
    exact hsum.eventually_lt_const hε
  -- a step meeting all three at once is what the filter's nonemptiness gives
  have hev2 : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), ‖r • A‖ / ((η : ℝ) + 2) < 1 :=
    hT2.eventually_lt_const one_pos
  have hev3 : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), (0 : ℝ) < r := self_mem_nhdsWithin
  obtain ⟨r, ⟨hr1, hr2⟩, hr3⟩ := ((hev1.and hev2).and hev3).exists
  exact ⟨r, hr3, hr1, hr2⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

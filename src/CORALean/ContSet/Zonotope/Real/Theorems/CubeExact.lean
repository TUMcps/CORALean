module

public import CORALean.ContSet.Zonotope.Real.Operations.Cube
public import CORALean.ContSet.Zonotope.Real.Theorems.MemConstruct
public import Mathlib.Analysis.Normed.Ring.Basic

@[expose] public section

/-!
# `□(ρ)` is exactly the sup-norm ball

What [1, Lemma 1] asserts in passing, that the ball `□(ρ)` of the infinity norm is a
zonotope: coordinate `i` of a point of `Zonotope.cube n ρ` is `ρ βᵢ` with `|βᵢ| ≤ 1`, and
every point of the ball is reached with `βᵢ = xᵢ / ρ`. `0 ≤ ρ` is needed for the ball to
be what the generators span: at a negative radius the ball is empty and the zonotope is not.

## Inputs
* `n` – dimension
* `ρ` – radius

## Hypotheses
* `hρ` – radius nonnegative

## Conclusion
* the cube zonotope is the closed ball of radius `ρ`

## References

* [1] [A. Girard. "Reachability of Uncertain Linear Systems Using Zonotopes". Hybrid Systems:
      Computation and Control,
      2005.](../../../../../../references/2005/girard-hscc-reachability-zonotopes.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Coordinate `i` of the cube's generator sum is `ρ βᵢ`. -/
private theorem Zonotope.aux_cube_sum_apply {n : ℕ} (ρ : ℝ) (β : Fin (Zonotope.cube n ρ).h → ℝ)
    (i : Fin n) : -- --- CONCL ---
    ∑ j, (Zonotope.cube n ρ).G j i * β j = ρ * β i := by -- --- PROOF ---
  show ∑ j : Fin n, (Pi.single j ρ : Vec ℝ n) i * β j = ρ * β i
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Ne.symm hj]
  · intro h
    exact absurd (Finset.mem_univ i) h


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Lemma 1]: `□(ρ)`, the sup-norm ball of radius `ρ ≥ 0`, is the zonotope `cube n ρ`. -/
theorem Zonotope.cube_exact (n : ℕ) {ρ : ℝ} (hρ : 0 ≤ ρ) : -- --- CONCL ---
    (Zonotope.cube n ρ).construct = Metric.closedBall (0 : Vec ℝ n) ρ := by -- --- PROOF ---
  ext x
  rw [Zonotope.mem_construct_iff, Metric.mem_closedBall, dist_zero_right,
    pi_norm_le_iff_of_nonneg hρ]
  have hc : ∀ i, (Zonotope.cube n ρ).c i = 0 := fun _ => rfl
  constructor
  · rintro ⟨β, hβ, hx⟩ i
    rw [Real.norm_eq_abs, hx i, hc, zero_add, Zonotope.aux_cube_sum_apply, abs_mul,
      abs_of_nonneg hρ]
    exact mul_le_of_le_one_right hρ (hβ i)
  -- every point of the ball, coordinate by coordinate a multiple of `ρ`
  · intro hx
    rcases hρ.eq_or_lt with h | h
    · refine ⟨0, fun _ => by simp, fun i => ?_⟩
      rw [hc, zero_add, Zonotope.aux_cube_sum_apply, ← h, zero_mul]
      have := hx i
      rw [← h, Real.norm_eq_abs] at this
      exact abs_nonpos_iff.mp this
    · refine ⟨fun i => x i / ρ, fun i => ?_, fun i => ?_⟩
      · rw [abs_div, abs_of_pos h, div_le_one h]
        exact (Real.norm_eq_abs _).symm ▸ hx i
      · rw [hc, zero_add, Zonotope.aux_cube_sum_apply]
        field_simp

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

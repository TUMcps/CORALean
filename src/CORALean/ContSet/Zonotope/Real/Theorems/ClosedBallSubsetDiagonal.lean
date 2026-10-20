module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Data.Matrix.Diagonal

@[expose] public section

/-!
# A ball is a zonotope in the supremum norm

`Vec ℝ n` carries the supremum norm, so its closed ball of radius `ε` about
the origin is the box `[-ε, ε]ⁿ`, and that box is the zonotope with one
generator `ε eᵢ` per coordinate. The direction proved is the one an error bound
needs: an error stated as a radius may be replaced by this zonotope, which is
what lets a Minkowski difference by it be computed at a representation.

Nothing is asked of `ε`: a negative radius leaves the ball empty.

## Inputs
* `ε` – radius

## Hypotheses
* none

## Conclusion
* the closed ball lies in the diagonal-generator zonotope
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-September-2026
-- Last update:   ---
-- Reviewed:      14-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The closed ball of radius `ε` lies in the zonotope whose generators are
`ε` times the unit vectors. -/
theorem Zonotope.closedBall_subset_diagonal (ε : ℝ) : -- --- CONCL ---
    Metric.closedBall (0 : Vec ℝ n) ε
      ⊆ (⟨n, 0, Matrix.diagonal fun _ => ε⟩ : Zonotope (Vec ℝ n)).construct := by -- --- PROOF ---
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right] at hx
  have hε : 0 ≤ ε := (norm_nonneg x).trans hx
  have hxi : ∀ i, |x i| ≤ ε := fun i => (Real.norm_eq_abs (x i) ▸ norm_le_pi_norm x i).trans hx
  -- each coordinate, measured against the radius, is its own coefficient
  refine ⟨fun i => x i / ε, fun i => ?_, ?_⟩
  · rw [abs_div, abs_of_nonneg hε]
    exact div_le_one_of_le₀ (hxi i) hε
  funext i
  show x i = (0 + ∑ j, (x j / ε) • (Matrix.diagonal fun _ => ε) j) i
  rw [zero_add, Finset.sum_apply, Finset.sum_eq_single i]
  · -- a zero radius pins the coordinate at the origin, where the quotient is `0` too
    rcases hε.eq_or_lt with h0 | hpos
    · have : x i = 0 := abs_nonpos_iff.mp (h0 ▸ hxi i)
      simp [this]
    · simp [Matrix.diagonal_apply_eq, div_mul_cancel₀ _ hpos.ne']
  · intro j _ hj
    simp [Matrix.diagonal_apply_ne _ hj]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

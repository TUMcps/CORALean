import CORALean.ContSet.Interval.Real.Operations.Mtimes

/-!
# `Interval.mtimes` over-approximates the image under a linear map

Each summand `M i k * x k` lies between the two endpoint products;
`mul_between_endpoints` is where `min`/`max` absorb the sign of `M i k`,
leaving one case split. Summing over `k` finishes it.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   02-September-2026
-- Last revision: ---

namespace CORALean.Real

open Matrix

variable {n m : ℕ}

/-- Scaling a point between two endpoints lands between the scaled endpoints,
whichever way the scale points. -/
theorem Interval.mul_between_endpoints {c lo hi x : ℝ} (h₁ : lo ≤ x) (h₂ : x ≤ hi) :
    min (c * lo) (c * hi) ≤ c * x ∧ c * x ≤ max (c * lo) (c * hi) := by
  rcases le_total 0 c with hc | hc
  · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_left h₁ hc),
           (mul_le_mul_of_nonneg_left h₂ hc).trans (le_max_right _ _)⟩
  · exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_left h₂ hc),
           (mul_le_mul_of_nonpos_left h₁ hc).trans (le_max_left _ _)⟩

theorem Interval.mtimes_outer (M : Mat ℝ m n) (I : Interval (Vec ℝ n)) :
    (M *ᵥ ·) '' I.construct ⊆ (Interval.mtimes M I).construct := by
  rintro _ ⟨x, hx, rfl⟩ i
  -- `entry` at a vector is the coordinate, definitionally
  have hxk : ∀ k, I.inf k ≤ x k ∧ x k ≤ I.sup k := fun k => hx k
  show (∑ k, min (M i k * I.inf k) (M i k * I.sup k)) ≤ ∑ k, M i k * x k
      ∧ (∑ k, M i k * x k) ≤ ∑ k, max (M i k * I.inf k) (M i k * I.sup k)
  exact ⟨Finset.sum_le_sum fun k _ =>
           (Interval.mul_between_endpoints (hxk k).1 (hxk k).2).1,
         Finset.sum_le_sum fun k _ =>
           (Interval.mul_between_endpoints (hxk k).1 (hxk k).2).2⟩

end CORALean.Real

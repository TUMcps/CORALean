import CORALean.Real.ContSet.Interval.Operations.API

/-!
# `Interval.mtimes` over-approximates the image under a linear map

Each summand `M i k * x k` lies between the two endpoint products;
`aux_mul_between_endpoints` is where `min`/`max` absorb the sign of `M i k`,
leaving one case split. Summing over `k` finishes it.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix

variable {n m : ℕ}

/-- Scaling a point between two endpoints lands between the scaled endpoints,
whichever way the scale points. -/
theorem Interval.aux_mul_between_endpoints {c lo hi x : ℝ} (h₁ : lo ≤ x) (h₂ : x ≤ hi) :
    min (c * lo) (c * hi) ≤ c * x ∧ c * x ≤ max (c * lo) (c * hi) := by
  rcases le_total 0 c with hc | hc
  · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_left h₁ hc),
           (mul_le_mul_of_nonneg_left h₂ hc).trans (le_max_right _ _)⟩
  · exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_left h₂ hc),
           (mul_le_mul_of_nonpos_left h₁ hc).trans (le_max_left _ _)⟩

theorem Interval.mtimes_outer (M : Mat ℝ m n) (I : Interval n) :
    (M *ᵥ ·) '' I.construct ⊆ (Interval.mtimes M I).construct := by
  rintro _ ⟨x, hx, rfl⟩ i
  simp only [Interval.mtimes, Matrix.mulVec, dotProduct]
  exact ⟨Finset.sum_le_sum fun k _ => (Interval.aux_mul_between_endpoints (hx k).1 (hx k).2).1,
         Finset.sum_le_sum fun k _ => (Interval.aux_mul_between_endpoints (hx k).1 (hx k).2).2⟩

end CORALean.Real

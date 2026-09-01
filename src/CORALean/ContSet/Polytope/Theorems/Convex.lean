import CORALean.ContSet.Polytope.VPolytope

/-!
# Both polytope representations are convex

A halfspace description is an intersection of halfspaces, each cut by one linear
functional; a vertex description is a set of convex combinations, and a weighted
average of two of them reweights to a third.

Holds for any constraints and any vertex list, the empty case included.
-/

-- Authors:       Tobias Ladner
-- Written:       01-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]

theorem Polytope.convex_construct (P : Polytope α) : Convex ℝ P.construct := by
  rintro x ⟨hx, hex⟩ y ⟨hy, hey⟩ a b ha hb hab
  refine ⟨fun i => ?_, fun i => ?_⟩
  · have h1 := mul_le_mul_of_nonneg_left (hx i) ha
    have h2 := mul_le_mul_of_nonneg_left (hy i) hb
    -- the weights sum to one, so the bound is its own weighted average
    have hb' : a * P.b i + b * P.b i = P.b i := by rw [← add_mul, hab, one_mul]
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    linarith
  · rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, hex i, hey i, ← add_mul, hab,
      one_mul]

theorem VPolytope.convex_construct (P : VPolytope α) : Convex ℝ P.construct := by
  rintro x ⟨β₁, hβ₁, hs₁, rfl⟩ y ⟨β₂, hβ₂, hs₂, rfl⟩ a b ha hb hab
  have hnn : ∀ j, 0 ≤ a * β₁ j + b * β₂ j := fun j =>
    add_nonneg (mul_nonneg ha (hβ₁ j)) (mul_nonneg hb (hβ₂ j))
  have hsum : ∑ j, (a * β₁ j + b * β₂ j) = 1 := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hs₁, hs₂, mul_one, mul_one, hab]
  have hval : ∑ j, (a * β₁ j + b * β₂ j) • P.V j
      = a • (∑ j, β₁ j • P.V j) + b • ∑ j, β₂ j • P.V j := by
    rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by rw [add_smul, smul_smul, smul_smul]
  exact ⟨fun j => a * β₁ j + b * β₂ j, hnn, hsum, hval.symm⟩

end CORALean.Real

module

public import CORALean.ContSet.VPolytope.Real.VPolytope
public import Mathlib.Analysis.Convex.Basic

@[expose] public section

/-!
# A vertex description is convex

A weighted average of two convex combinations reweights to a third. Holds for
any vertex list, the empty one included.

Proved directly rather than from the hull, since `construct_eq_convexHull` is
what needs it.
-/

-- Authors:       Claude Opus 5
-- Written:       01-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem VPolytope.convex_construct (P : VPolytope α) : Convex ℝ P.construct := by -- --- PROOF ---
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


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

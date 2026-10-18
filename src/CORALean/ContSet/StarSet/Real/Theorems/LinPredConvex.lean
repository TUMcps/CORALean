module

public import CORALean.ContSet.StarSet.Real.StarSet
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# CORA's star-set predicate is convex

The box and every row are linear in the coefficients, so a convex combination of two coefficient
vectors meeting them meets them with the same combination.
-/

-- Authors:       Claude Sonnet 5.5, Claude Opus 5.5
-- Written:       15-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- `C α ≤ d, l ≤ α ≤ u` is convex. -/
theorem StarSet.LinPred.convex_construct {m : ℕ} (p : StarSet.LinPred m) :
    Convex ℝ p.construct := by -- --- PROOF ---
  rintro α ⟨hα, hα'⟩ β ⟨hβ, hβ'⟩ a b ha hb hab
  refine ⟨fun k => ⟨?_, ?_⟩, fun r hr => ?_⟩
  · have h := add_le_add (mul_le_mul_of_nonneg_left (hα k).1 ha)
      (mul_le_mul_of_nonneg_left (hβ k).1 hb)
    rw [← add_mul, hab, one_mul] at h
    simpa using h
  · have h := add_le_add (mul_le_mul_of_nonneg_left (hα k).2 ha)
      (mul_le_mul_of_nonneg_left (hβ k).2 hb)
    rw [← add_mul, hab, one_mul] at h
    simpa using h
  · -- every row is linear in the coefficients, so the combination satisfies it
    have h1 := hα' r hr
    have h2 := hβ' r hr
    have : ∑ k, r.1 k * (a • α + b • β) k
        = a * ∑ k, r.1 k * α k + b * ∑ k, r.1 k * β k := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [this]
    have h := add_le_add (mul_le_mul_of_nonneg_left h1 ha) (mul_le_mul_of_nonneg_left h2 hb)
    rwa [← add_mul, hab, one_mul] at h

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.ContSet.StarSet.Real.StarSet
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# A star set is convex

The predicate on the factors is linear, so a convex combination of two factor vectors satisfies it
with the same combination of the two points.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem StarSet.convex_construct {n : ℕ} (s : StarSet n) :
    Convex ℝ s.construct := by -- --- PROOF ---
  -- two points, with their factor vectors; the convex combination of the factors is the witness
  rintro x ⟨α, hα, hα', hxα⟩ y ⟨β, hβ, hβ', hyβ⟩ a b ha hb hab
  refine ⟨fun k => a * α k + b * β k, fun k => ⟨?_, ?_⟩, fun r hr => ?_, fun i => ?_⟩
  · have h := add_le_add (mul_le_mul_of_nonneg_left (hα k).1 ha)
      (mul_le_mul_of_nonneg_left (hβ k).1 hb)
    rwa [← add_mul, hab, one_mul] at h
  · have h := add_le_add (mul_le_mul_of_nonneg_left (hα k).2 ha)
      (mul_le_mul_of_nonneg_left (hβ k).2 hb)
    rwa [← add_mul, hab, one_mul] at h
  · -- every row is linear in the factors, so the combination satisfies it
    have h1 := hα' r hr
    have h2 := hβ' r hr
    have : ∑ k, r.1 k * (a * α k + b * β k)
        = a * ∑ k, r.1 k * α k + b * ∑ k, r.1 k * β k := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [this]
    have h := add_le_add (mul_le_mul_of_nonneg_left h1 ha) (mul_le_mul_of_nonneg_left h2 hb)
    rwa [← add_mul, hab, one_mul] at h
  · -- the point is the same combination of the two points
    have : ∑ k, s.G i k * (a * α k + b * β k)
        = a * ∑ k, s.G i k * α k + b * ∑ k, s.G i k * β k := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hxα i, hyβ i, this]
    have : s.c i = a * s.c i + b * s.c i := by rw [← add_mul, hab, one_mul]
    linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.ContSet.ContSet.Definitions.ConvexSet
public import CORALean.ContSet.StarSet.Real.StarSet
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# A star set of a convex predicate is convex

The set is the image of the predicate's coefficients under the affine map `α ↦ c + G α`, so a
convex combination of two points is the point of the same combination of their coefficients,
which a convex predicate holds of. A predicate that is not convex, a `LevelSet` such as
`{α | α₀² = 1}`, gives a star set that is not.
-/

-- Authors:       Claude Sonnet 5.5, Claude Opus 5.5
-- Written:       15-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open ContSet


-- =======================================  MAIN THEOREM  ======================================= --

/-- A star set over a convex predicate is convex. -/
theorem StarSet.convex_construct {P : ℕ → Type} [∀ m, ContSet (P m) (Vec ℝ m)]
    [∀ m, ConvexSet (P m) (Vec ℝ m)] {n : ℕ} (s : StarSet P n) :
    Convex ℝ s.construct := by -- --- PROOF ---
  -- two points, with their coefficients; the convex combination of the coefficients is the witness
  rintro x ⟨α, hα, hxα⟩ y ⟨β, hβ, hyβ⟩ a b ha hb hab
  refine ⟨a • α + b • β, ConvexSet.convex_construct s.pred hα hβ ha hb hab, fun i => ?_⟩
  -- the point is the same combination of the two points
  have : ∑ k, s.G i k * (a • α + b • β) k
      = a * ∑ k, s.G i k * α k + b * ∑ k, s.G i k * β k := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [this]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hxα i, hyβ i]
  have : s.c i = a * s.c i + b * s.c i := by rw [← add_mul, hab, one_mul]
  linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

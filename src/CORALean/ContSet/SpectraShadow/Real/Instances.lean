import CORALean.ContSet.ContSet.Definitions.ConvexSet
import CORALean.ContSet.SpectraShadow.Real.Theorems.LinCombOuter
import CORALean.ContSet.SpectraShadow.Real.Theorems.MtimesExact

/-!
# What `SpectraShadow` instantiates

`ContSet`, `ConvexSet` — a shadow of a convex cone's slice — `Plus` and `Mtimes`,
both from the exactness theorems, which the classes' outer obligations only keep
the first half of, and `LinComb` at the convex hull `convHull_`, whose set is exact.

No `CompactSet`: the set is unbounded as soon as the inequality leaves a
variable free, and boundedness is not something the type records. No `Intersection`
or `Reduce`: `inter` and the exactness theorem exist, but are not collected into the class
yet, and `Reduce` has nothing to compute that is cheap.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- ========================================  INSTANCES  ========================================= --

instance : ContSet (SpectraShadow α) α := ⟨SpectraShadow.construct⟩

instance : ConvexSet (SpectraShadow α) α := ⟨SpectraShadow.convex_construct⟩

instance : Plus (SpectraShadow α) α where
  plus := SpectraShadow.plus
  plus_outer S₁ S₂ := (SpectraShadow.plus_exact S₁ S₂).subset

instance : Mtimes (Mat ℝ) (fun n => SpectraShadow (Vec ℝ n)) where
  mtimes := SpectraShadow.mtimes
  mtimes_outer M S := by
    simp only [ContSet.construct_mat, Scalar.toRealMat_real, Set.biUnion_singleton]
    exact (SpectraShadow.mtimes_exact M S).subset

/-- CORA's `linComb` is not the convex hull, but for a shadow, which is convex, the segments are
inside it, and `convHull_` is what `enclose` and `or` ask for. -/
instance {n : ℕ} : LinComb (SpectraShadow (Vec ℝ n)) (Vec ℝ n) where
  linComb := SpectraShadow.convHull_
  linComb_outer := SpectraShadow.segments_subset_convHull

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

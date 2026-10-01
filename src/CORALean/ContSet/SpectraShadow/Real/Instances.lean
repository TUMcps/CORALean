import CORALean.ContSet.ContSet.Definitions.ConvexSet
import CORALean.ContSet.SpectraShadow.Real.Theorems.API

/-!
# What `SpectraShadow` instantiates

`ContSet`, `ConvexSet` — a shadow of a convex cone's slice — `Plus` and `Mtimes`,
both from the exactness theorems, which the classes' outer obligations only keep
the first half of.

No `CompactSet`: the set is unbounded as soon as the inequality leaves a
variable free, and boundedness is not something the type records. No `Intersection`,
`LinComb` or `Reduce`: the first needs the existential-sum form CORA keeps beside
`A`, `c` and `G`, and the other two have nothing to compute that is cheap.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


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

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

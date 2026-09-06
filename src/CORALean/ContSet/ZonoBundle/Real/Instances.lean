import CORALean.ContSet.ContSet.ConvexSet
import CORALean.ContSet.ZonoBundle.Real.Theorems.AndExact
import CORALean.ContSet.ZonoBundle.Real.Theorems.Convex
import CORALean.ContSet.ZonoBundle.Real.Theorems.PlusOuter
import CORALean.ContSet.ZonoBundle.Real.Theorems.MtimesOuter

/-!
# What `ZonoBundle` instantiates

`ContSet`, `ConvexSet` — an intersection of convex sets — `Plus` and `Mtimes`
from the enclosure operations, and `And` from `and_exact`: appending the two
families of zonotopes is exact, at any real module.

`CompactSet` is not an instance: at `k = 0` the set is `univ`, not compact, so
the class's unconditional obligation cannot be discharged. `isCompact_construct`
states the conditional fact instead, at `0 < B.k`.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   06-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- ========================================  INSTANCES  ========================================= --

instance : ContSet (ZonoBundle α) α := ⟨ZonoBundle.construct⟩

instance : ConvexSet (ZonoBundle α) α := ⟨ZonoBundle.convex_construct⟩

instance : Plus (ZonoBundle α) α where
  plus := ZonoBundle.plus
  plus_outer := ZonoBundle.plus_outer

instance : And (ZonoBundle α) α where
  and := ZonoBundle.and
  and_outer B₁ B₂ := (ZonoBundle.and_exact B₁ B₂).symm.subset

instance : Mtimes (Mat ℝ) (fun n => ZonoBundle (Vec ℝ n)) where
  mtimes := ZonoBundle.mtimes
  mtimes_outer M B := by
    simp only [ContSet.construct_mat, Scalar.toRealMat_real, Set.biUnion_singleton]
    exact ZonoBundle.mtimes_outer M B

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

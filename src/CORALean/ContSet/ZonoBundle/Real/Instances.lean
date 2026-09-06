import CORALean.ContSet.ContSet.ConvexSet
import CORALean.ContSet.ZonoBundle.Real.Theorems.Convex
import CORALean.ContSet.ZonoBundle.Real.Theorems.PlusOuter
import CORALean.ContSet.ZonoBundle.Real.Theorems.MtimesOuter

/-!
# What `ZonoBundle` instantiates

`ContSet`, `ConvexSet` — an intersection of convex sets — and `Plus` and
`Mtimes` from the enclosure operations. `and` has no class to land in (#10),
so it stays a plain theorem.

`CompactSet` is not an instance: at `k = 0` the set is `univ`, not compact, so
the class's unconditional obligation cannot be discharged. `isCompact_construct`
states the conditional fact instead, at `0 < B.k`.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
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

instance : Mtimes (Mat ℝ) (fun n => ZonoBundle (Vec ℝ n)) where
  mtimes := ZonoBundle.mtimes
  mtimes_outer M B := by
    simp only [ContSet.construct_mat, Scalar.toRealMat_real, Set.biUnion_singleton]
    exact ZonoBundle.mtimes_outer M B

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

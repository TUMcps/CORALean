module

public import CORALean.ContSet.ContSet.Definitions.ConvexSet
public import CORALean.ContSet.ZonoBundle.Real.Theorems.IntersectionExact
public import CORALean.ContSet.ZonoBundle.Real.Theorems.Convex
public import CORALean.ContSet.ZonoBundle.Real.Theorems.PlusOuter
public import CORALean.ContSet.ZonoBundle.Real.Theorems.LinCombOuter
public import CORALean.ContSet.ZonoBundle.Real.Theorems.MtimesOuter
public import CORALean.ContSet.ZonoBundle.Real.Theorems.MtimesMatZonotopeOuter
public import CORALean.ContSet.Zonotope.Real.Instances
public import CORALean.ContSet.ZonoBundle.Real.Theorems.MapExact
public import CORALean.ContSet.ZonoBundle.Real.Theorems.OfPointMem
public import CORALean.ContSet.ZonoBundle.Real.Theorems.ReduceOuter

@[expose] public section

/-!
# What `ZonoBundle` instantiates

`ContSet`, `ConvexSet` — an intersection of convex sets — `Plus`, `LinComb`
and `Mtimes`, the last at a point matrix and at a matrix zonotope alike, from
the enclosure operations, and `Intersection` from `intersection_exact`:
appending the two families of zonotopes is exact, at any real module.
`OfPoint` bundles one point-zonotope, and `Reindex` lifts `Zonotope`'s at
`reindexLin e`, which `map_exact` needs *bijective* rather than merely
injective — `e`'s own inverse supplies that. `Reduce` drops components,
which only enlarges the set, so it needs no error box, unlike every other
`reduce` in the tree.

`CompactSet` is not an instance: at `k = 0` the set is `univ`, not compact, so
the class's unconditional obligation cannot be discharged. `isCompact_construct`
states the conditional fact instead, at `0 < zB.k`. No `MinkDiff` either — that
needs `Zonotope.minkDiff`, an open design decision on #85.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   07-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `reindexLin e.symm` is a two-sided inverse of `reindexLin e`: `e`'s own
cancellation laws move straight through the coordinate swap. -/
theorem aux_reindexLin_bijective {n m : ℕ} (e : Fin m ≃ Fin n) :
    Function.Bijective (reindexLin e) := by -- --- PROOF ---
  have hl : Function.LeftInverse (reindexLin e.symm) (reindexLin e) :=
    fun x => funext fun i => by simp [reindexLin]
  have hr : Function.LeftInverse (reindexLin e) (reindexLin e.symm) :=
    fun x => funext fun i => by simp [reindexLin]
  exact ⟨hl.injective, hr.surjective⟩


-- ========================================  INSTANCES  ========================================= --

instance : ContSet (ZonoBundle α) α := ⟨ZonoBundle.construct⟩

instance : ConvexSet (ZonoBundle α) α := ⟨ZonoBundle.convex_construct⟩

instance : Plus (ZonoBundle α) α where
  plus := ZonoBundle.plus
  plus_outer := ZonoBundle.plus_outer

noncomputable instance : LinComb (ZonoBundle α) α where
  linComb := ZonoBundle.linComb
  linComb_outer := ZonoBundle.linComb_outer

instance : Intersection (ZonoBundle α) α where
  intersection := ZonoBundle.intersection
  intersection_outer zB₁ zB₂ := (ZonoBundle.intersection_exact zB₁ zB₂).symm.subset

instance : OfPoint (ZonoBundle α) α where
  ofPoint := ZonoBundle.ofPoint
  mem_ofPoint := ZonoBundle.mem_ofPoint

/-- `map` at the relabelling: `reindexLin e` is bijective, so `map_exact`
applies, unlike `Zonotope`'s instance of it, which needs no hypothesis. -/
instance : Reindex (fun n => ZonoBundle (Vec ℝ n)) where
  reindex e zB := ZonoBundle.map (reindexLin e) zB
  reindex_exact e zB := ZonoBundle.map_exact (reindexLin e) (aux_reindexLin_bijective e) zB

instance : Mtimes (Mat ℝ) (fun n => ZonoBundle (Vec ℝ n)) where
  mtimes := ZonoBundle.mtimes
  mtimes_outer M zB := by
    simp only [ContSet.construct_mat, Scalar.toRealMat_real, Set.biUnion_singleton]
    exact ZonoBundle.mtimes_outer M zB

/-- The same operation at a matrix zonotope, which keeps the correlations an
interval matrix would throw away. Componentwise, as `mtimes` is. -/
noncomputable instance : Mtimes 𝕄𝒵 (fun n => ZonoBundle (Vec ℝ n)) where
  mtimes := ZonoBundle.mtimesMatZonotope
  mtimes_outer M zB := ZonoBundle.mtimesMatZonotope_outer M zB

instance : Reduce (ZonoBundle α) α where
  reduce := ZonoBundle.reduce
  reduce_outer := ZonoBundle.reduce_outer

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

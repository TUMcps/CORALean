module

public import CORALean.ContSet.ContSet.Definitions.Interfaces
public import CORALean.ContSet.ZonoBundle.Real.Theorems.IntersectionExact
public import CORALean.ContSet.ZonoBundle.Real.Theorems.Basic
public import CORALean.ContSet.ZonoBundle.Real.Operations.Plus
public import CORALean.ContSet.ZonoBundle.Real.Operations.LinComb
public import CORALean.ContSet.ZonoBundle.Real.Operations.Mtimes
public import CORALean.ContSet.ZonoBundle.Real.Operations.MtimesMatZonotope
public import CORALean.ContSet.ZonoBundle.Real.Operations.Map
public import CORALean.ContSet.ZonoBundle.Real.Operations.Reduce
public import CORALean.ContSet.Zonotope.Real.Instances
public import CORALean.ContSet.Zonotope.Real.Theorems.MapExact
public import CORALean.ContSet.SetIntersection.Theorems.MemberwiseOuter
public import CORALean.ContSet.SetIntersection.Theorems.MemberwiseImageExact
public import CORALean.ContSet.SetIntersection.Theorems.PairwiseOuter
public import CORALean.ContSet.ContSet.Theorems.Basic

@[expose] public section

/-!
# What `ZonoBundle` instantiates

A bundle is `SetIntersection` at its members, so every guarantee here is a general theorem of that
class at the members' own: `ConvexSet` is `SetIntersection.convex_construct`; `Plus` and `LinComb`
are `pairwise_outer` at `Zonotope.plus_exact` and `Zonotope.linComb_outer`; `Mtimes`, at a point
matrix and at a matrix zonotope, and `Reduce`, which drops members and needs no error box, are
`memberwise_outer`; `Reindex` is `memberwise_image_exact` at `reindexLin e`. `Intersection` is
`intersection_exact`, appending the two families; `OfPoint` bundles one point-zonotope. `CompactSet`
is not an instance: at `k = 0` the set is `univ`, so the unconditional obligation fails;
`SetIntersection.isCompact_construct` states the conditional fact. No `MinkDiff` either (#85).
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       06-September-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix Pointwise

variable {α : Type} [AddCommGroup α] [Module ℝ α]

/-- The zonotope-bundle family over vectors: pins `(S := 𝒵ℬ)`. -/
scoped notation "𝒵ℬ" => fun n => ZonoBundle (Vec ℝ n)


-- ========================================  INSTANCES  ========================================= --

instance : ContSet (ZonoBundle α) α := ⟨ZonoBundle.construct⟩

instance : ConvexSet (ZonoBundle α) α :=
  ⟨fun zB => SetIntersection.convex_construct zB.toSetIntersection⟩

/-- Every pair of members summed, each sum exact. -/
instance : Plus (ZonoBundle α) α where
  plus := ZonoBundle.plus
  plus_outer _ _ := SetIntersection.pairwise_outer (· + ·)
    (fun _ _ _ _ => Set.add_subset_add) fun p =>
      ⟨(finProdFinEquiv.symm p).1, (finProdFinEquiv.symm p).2, (Zonotope.plus_exact _ _).subset⟩

/-- Every pair of members combined, each by `Zonotope.linComb_outer`. -/
noncomputable instance : LinComb (ZonoBundle α) α where
  linComb := ZonoBundle.linComb
  linComb_outer _ _ := SetIntersection.pairwise_outer Set.linComb
    (fun _ _ _ _ => setLinComb_mono) fun p =>
      ⟨(finProdFinEquiv.symm p).1, (finProdFinEquiv.symm p).2, Zonotope.linComb_outer _ _⟩

instance : Intersection (ZonoBundle α) α where
  intersection := ZonoBundle.intersection
  intersection_outer zB₁ zB₂ := (ZonoBundle.intersection_exact zB₁ zB₂).symm.subset

instance : OfPoint (ZonoBundle α) α where
  ofPoint := ZonoBundle.ofPoint
  mem_ofPoint := ZonoBundle.mem_ofPoint

/-- `map` at the relabelling: `reindexLin e` is bijective, so the bundle's image is exact,
unlike `Zonotope`'s instance of it, which needs no hypothesis. -/
instance : Reindex (𝒵ℬ) where
  reindex e zB := ZonoBundle.map (reindexLin e) zB
  reindex_exact e zB := SetIntersection.memberwise_image_exact (reindexLin e)
    (reindexLin_bijective e) fun i => (Zonotope.map_exact (reindexLin e) (zB.Z i)).symm

instance : Mtimes (Mat ℝ) (𝒵ℬ) where
  mtimes := ZonoBundle.mtimes
  mtimes_outer M zB := by
    simp only [ContSet.construct_mat, Scalar.toRealMat_real, Set.biUnion_singleton]
    exact SetIntersection.memberwise_outer _ Set.monotone_image fun i =>
      ⟨i, (Zonotope.mtimes_exact M (zB.Z i)).subset⟩

/-- The same operation at a matrix zonotope, which keeps the correlations an
interval matrix would throw away. Componentwise, as `mtimes` is. -/
noncomputable instance : Mtimes 𝕄𝒵 (𝒵ℬ) where
  mtimes := ZonoBundle.mtimesMatZonotope
  mtimes_outer M zB := SetIntersection.memberwise_outer (fun X => ⋃ A ∈ M.construct, (A *ᵥ ·) '' X)
    (fun _ _ h => Set.biUnion_mono subset_rfl fun _ _ => Set.image_mono h) fun i =>
      ⟨i, Zonotope.mtimesMatZonotope_outer M (zB.Z i)⟩

/-- Drops members, which only enlarges the intersection. -/
instance : Reduce (ZonoBundle α) α where
  reduce := ZonoBundle.reduce
  reduce_outer zB o := SetIntersection.memberwise_outer id monotone_id fun i =>
    ⟨Fin.castLE (min_le_left zB.k o) i, subset_rfl⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.ContSet.ContSet.Definitions.ConvexSet
public import CORALean.ContSet.Interval.Float.Instances
public import CORALean.ContSet.ZonoBundle.Float.Operations.Materialise
public import CORALean.ContSet.ZonoBundle.Float.Theorems.Basic
public import CORALean.ContSet.ZonoBundle.Float.Theorems.IntersectionExact
public import CORALean.ContSet.ZonoBundle.Float.Operations.LinComb
public import CORALean.ContSet.ZonoBundle.Float.Operations.MtimesIntervalMat
public import CORALean.ContSet.ZonoBundle.Float.Operations.Mtimes
public import CORALean.ContSet.ZonoBundle.Float.Operations.Plus
public import CORALean.ContSet.ZonoBundle.Float.Operations.Reduce
public import CORALean.ContSet.ZonoBundle.Float.Operations.Reindex
public import CORALean.ContSet.Zonotope.Float.Instances
public import CORALean.ContSet.Zonotope.Float.Theorems.LinCombOuter
public import CORALean.ContSet.Zonotope.Float.Theorems.MtimesIntervalMatOuter
public import CORALean.ContSet.Zonotope.Float.Theorems.MtimesOuter
public import CORALean.ContSet.Zonotope.Float.Theorems.PlusOuter
public import CORALean.ContSet.Zonotope.Float.Theorems.ReindexExact
public import CORALean.ContSet.SetIntersection.Theorems.Basic
public import CORALean.ContSet.SetIntersection.Theorems.MemberwiseOuter
public import CORALean.ContSet.SetIntersection.Theorems.MemberwiseImageExact
public import CORALean.ContSet.SetIntersection.Theorems.PairwiseOuter
public import CORALean.ContSet.ContSet.Theorems.Basic

@[expose] public section

/-!
# What the float `ZonoBundle` instantiates

`ContSet` directly, not through `InflatedContSet`: the members carry the boxes,
and `ZonoBundle.lean` says why no bundle-wide one stands in for them. Then, as over ℝ, each a
general theorem of `SetIntersection` at the float members' own guarantees: `ConvexSet`
(`convex_construct`), `Plus` and `LinComb` (`pairwise_outer`), `Reduce` and `Mtimes` at a point
and at an interval matrix (`memberwise_outer`), `Reindex` (`memberwise_image_exact`), and
`Intersection` (`intersection_exact`).

Not `OfPoint`: it asks for an arbitrary *real* point, which no float
representation in this tree can store, and none instantiates it. Not `Mtimes` at
a matrix zonotope, `Zonotope` having no float `mtimesMatZonotope` to apply
componentwise. No `MinkDiff`, for the exact layer's reason — it needs a zonotope
difference, an open design decision on #85. No `CompactSet`, `k = 0` denoting
`univ`: compactness is the general `SetIntersection.isCompact_construct`, given a member.

A bundle and each member in it are closures over what an operation was given, so
every field below materialises, exactly as `Zonotope`'s do.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       07-September-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix Pointwise

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]

/-- The zonotope-bundle family over vectors.
The scalar is an argument: a notation cannot capture the section
variable `𝕋`, so `(S := 𝒵ℬ[𝕋])`. -/
scoped notation "𝒵ℬ[" t "]" => fun n => ZonoBundle (Vec t n)


-- ========================================  INSTANCES  ========================================= --

/-- One instance at every ambient type, as `Zonotope`'s `InflatedContSet` is. -/
instance {α β ι : Type} [RealImage α β] [AddCommGroup β] [Module ℝ β] [Entrywise β ι] :
    ContSet (ZonoBundle α) β := ⟨ZonoBundle.construct⟩

/-- An intersection of convex sets, each member's error box included in what
that member denotes. -/
instance {n : ℕ} : ConvexSet (ZonoBundle (Vec 𝕋 n)) (Vec ℝ n) :=
  ⟨fun zB => SetIntersection.convex_construct zB.toSetIntersection⟩

instance {n : ℕ} : Plus (ZonoBundle (Vec 𝕋 n)) (Vec ℝ n) where
  plus zB₁ zB₂ := (zB₁.plus zB₂).materialise
  plus_outer zB₁ zB₂ := by
    rw [ZonoBundle.materialise_eq]
    exact SetIntersection.pairwise_outer (· + ·) (fun _ _ _ _ => Set.add_subset_add) fun p =>
      ⟨(finProdFinEquiv.symm p).1, (finProdFinEquiv.symm p).2, Zonotope.plus_outer _ _⟩

instance {n : ℕ} : LinComb (ZonoBundle (Vec 𝕋 n)) (Vec ℝ n) where
  linComb zB₁ zB₂ := (zB₁.linComb zB₂).materialise
  linComb_outer zB₁ zB₂ := by
    rw [ZonoBundle.materialise_eq]
    exact SetIntersection.pairwise_outer Set.linComb (fun _ _ _ _ => setLinComb_mono) fun p =>
      ⟨(finProdFinEquiv.symm p).1, (finProdFinEquiv.symm p).2, Zonotope.linComb_outer _ _⟩

/-- Exact, as over ℝ: appending two families runs no arithmetic. The class
obligation keeps only the outer half of `intersection_exact`. -/
instance {n : ℕ} : Intersection (ZonoBundle (Vec 𝕋 n)) (Vec ℝ n) where
  intersection zB₁ zB₂ := (zB₁.intersection zB₂).materialise
  intersection_outer zB₁ zB₂ := by
    rw [ZonoBundle.materialise_eq]
    exact (ZonoBundle.intersection_exact zB₁ zB₂).symm.subset

/-- Members are dropped, never absorbed, so this needs no error box, unlike
`Zonotope.reduce`, which boxes the generators it discards. -/
instance {n : ℕ} : Reduce (ZonoBundle (Vec 𝕋 n)) (Vec ℝ n) where
  reduce zB o := (zB.reduce o).materialise
  reduce_outer zB o := by
    rw [ZonoBundle.materialise_eq]
    exact SetIntersection.memberwise_outer id monotone_id fun i =>
      ⟨Fin.castLE (min_le_left zB.k o) i, subset_rfl⟩

instance : Reindex 𝒵ℬ[𝕋] where
  reindex e zB := (ZonoBundle.reindex e zB).materialise
  reindex_exact e zB := by
    rw [ZonoBundle.materialise_eq]
    exact SetIntersection.memberwise_image_exact (reindexLin e) (reindexLin_bijective e) fun i =>
      Zonotope.reindex_exact e (zB.Z i)

instance : Mtimes (Mat 𝕋) 𝒵ℬ[𝕋] where
  mtimes M zB := (ZonoBundle.mtimes M zB).materialise
  mtimes_outer M zB := by
    simp only [ContSet.construct_mat, Set.biUnion_singleton, ZonoBundle.materialise_eq]
    exact SetIntersection.memberwise_outer _ Set.monotone_image fun i =>
      ⟨i, Zonotope.mtimes_outer M (zB.Z i)⟩

/-- The same operation at a float interval matrix, member by member, as `Zonotope`'s is. -/
instance : Mtimes ℐ[𝕋] 𝒵ℬ[𝕋] where
  mtimes IM zB := (ZonoBundle.mtimesIntervalMat IM zB).materialise
  mtimes_outer IM zB := by
    rw [ZonoBundle.materialise_eq]
    exact SetIntersection.memberwise_outer (fun X => ⋃ A ∈ IM.construct, (A *ᵥ ·) '' X)
      (fun _ _ h => Set.biUnion_mono subset_rfl fun _ _ => Set.image_mono h) fun i =>
        ⟨i, Zonotope.mtimesIntervalMat_outer IM (zB.Z i)⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

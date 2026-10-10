import CORALean.ContSet.ContSet.Definitions.ConvexSet
import CORALean.ContSet.Interval.Float.Instances
import CORALean.ContSet.ZonoBundle.Float.Theorems.Convex
import CORALean.ContSet.ZonoBundle.Float.Theorems.IntersectionExact
import CORALean.ContSet.ZonoBundle.Float.Theorems.PlusOuter
import CORALean.ContSet.ZonoBundle.Float.Theorems.LinCombOuter
import CORALean.ContSet.ZonoBundle.Float.Theorems.MtimesOuter
import CORALean.ContSet.ZonoBundle.Float.Theorems.MtimesIntervalMatOuter
import CORALean.ContSet.ZonoBundle.Float.Theorems.ReindexExact
import CORALean.ContSet.ZonoBundle.Float.Theorems.ReduceOuter

/-!
# What the float `ZonoBundle` instantiates

`ContSet` directly, not through `InflatedContSet`: the members carry the boxes,
and `ZonoBundle.lean` says why no bundle-wide one stands in for them. Then
`ConvexSet`, and `Plus`, `LinComb`, `Reduce`, `Reindex`, `Intersection` and `Mtimes` at a
point matrix, as over ℝ.

Not `OfPoint`: it asks for an arbitrary *real* point, which no float
representation in this tree can store, and none instantiates it. Not `Mtimes` at
a matrix zonotope, `Zonotope` having no float `mtimesMatZonotope` to apply
componentwise. No `MinkDiff`, for the exact layer's reason — it needs a zonotope
difference, an open design decision on #85. No `CompactSet`, `k = 0` denoting
`univ`: compactness is a theorem under `0 < zB.k` instead.

A bundle and each member in it are closures over what an operation was given, so
every field below materialises, exactly as `Zonotope`'s do.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   10-October-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- ========================================  INSTANCES  ========================================= --

/-- One instance at every ambient type, as `GZonotope`'s `InflatedContSet` is. -/
instance {α β ι : Type} [RealImage α β] [AddCommGroup β] [Module ℝ β] [Entrywise β ι] :
    ContSet (GZonoBundle α) β := ⟨GZonoBundle.construct⟩

/-- An intersection of convex sets, each member's error box included in what
that member denotes. -/
instance {n : ℕ} : ConvexSet (ZonoBundle 𝕋 n) (Vec ℝ n) := ⟨ZonoBundle.convex_construct⟩

instance {n : ℕ} : Plus (ZonoBundle 𝕋 n) (Vec ℝ n) where
  plus zB₁ zB₂ := (zB₁.plus zB₂).materialise
  plus_outer zB₁ zB₂ := by
    rw [ZonoBundle.materialise_eq]
    exact ZonoBundle.plus_outer zB₁ zB₂

instance {n : ℕ} : LinComb (ZonoBundle 𝕋 n) (Vec ℝ n) where
  linComb zB₁ zB₂ := (zB₁.linComb zB₂).materialise
  linComb_outer zB₁ zB₂ := by
    rw [ZonoBundle.materialise_eq]
    exact ZonoBundle.linComb_outer zB₁ zB₂

/-- Exact, as over ℝ: appending two families runs no arithmetic. The class
obligation keeps only the outer half of `intersection_exact`. -/
instance {n : ℕ} : Intersection (ZonoBundle 𝕋 n) (Vec ℝ n) where
  intersection zB₁ zB₂ := (zB₁.intersection zB₂).materialise
  intersection_outer zB₁ zB₂ := by
    rw [ZonoBundle.materialise_eq]
    exact (ZonoBundle.intersection_exact zB₁ zB₂).symm.subset

/-- Members are dropped, never absorbed, so this needs no error box, unlike
`Zonotope.reduce`, which boxes the generators it discards. -/
instance {n : ℕ} : Reduce (ZonoBundle 𝕋 n) (Vec ℝ n) where
  reduce zB o := (zB.reduce o).materialise
  reduce_outer zB o := by
    rw [ZonoBundle.materialise_eq]
    exact ZonoBundle.reduce_outer zB o

instance : Reindex (ZonoBundle 𝕋) where
  reindex e zB := (ZonoBundle.reindex e zB).materialise
  reindex_exact e zB := by
    rw [ZonoBundle.materialise_eq]
    exact ZonoBundle.reindex_exact e zB

instance : Mtimes (Mat 𝕋) (ZonoBundle 𝕋) where
  mtimes M zB := (ZonoBundle.mtimes M zB).materialise
  mtimes_outer M zB := by
    simp only [ContSet.construct_mat, Set.biUnion_singleton, ZonoBundle.materialise_eq]
    exact ZonoBundle.mtimes_outer M zB

/-- The same operation at a float interval matrix, member by member, as `Zonotope`'s is. -/
instance : Mtimes (fun m n => Interval (Mat 𝕋 m n)) (ZonoBundle 𝕋) where
  mtimes IM zB := (ZonoBundle.mtimesIntervalMat IM zB).materialise
  mtimes_outer IM zB := by
    rw [ZonoBundle.materialise_eq]
    exact ZonoBundle.mtimesIntervalMat_outer IM zB

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

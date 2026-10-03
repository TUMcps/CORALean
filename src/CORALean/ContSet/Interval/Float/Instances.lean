import CORALean.ContSet.ContSet.Definitions.CompactSet
import CORALean.ContSet.ContSet.Definitions.ConvexSet
import CORALean.ContSet.Interval.Float.Operations.IntersectionExact
import CORALean.ContSet.Interval.Float.Theorems.IsCompact
import CORALean.ContSet.Interval.Float.Theorems.LinCombOuter
import CORALean.ContSet.Interval.Float.Operations.Center
import CORALean.ContSet.Interval.Float.Theorems.MemPoint
import CORALean.ContSet.Interval.Float.Theorems.MinkDiffInner
import CORALean.ContSet.Interval.Float.Theorems.MtimesIntervalMatOuter
import CORALean.ContSet.Interval.Float.Theorems.MtimesOuter
import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
import CORALean.ContSet.Interval.Float.Theorems.ReindexExact
import CORALean.ContSet.Interval.Real.Theorems.Convex
import CORALean.ContSet.Interval.Real.Theorems.IsCompact
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# What `Interval` instantiates

The same obligations the exact layer discharges, since a float interval denotes a
set of real points just as an exact one does; only the scalar the operations run
in differs. `ConvexSet` and `CompactSet` cost no float proof: `construct` is
`nominal.construct` by definition, so the exact layer's theorems apply to
`I.nominal` unchanged. `Intersection` is exact here too, nothing rounding.

`reduce` gives up no order, as over ℝ: an interval has none to give up. No
`OfPoint`: it would round a real point into `𝕋`, an operation this layer lacks; `OfScalarPoint`
takes the point already in `𝕋`, which `Interval.point` holds exactly.

Every field returns a `materialise`d interval. The bounds are function types, so
the one an operation returns is a closure over the one it was given, and a loop
that iterates operations would rebuild its whole history on every read.
`materialise_eq` is the identity, so each proof below is the operation's own
guarantee after one rewrite. It is here rather than in `Operations/` because this
is where a set is handed back to a caller that may loop.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   24-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ========================================  INSTANCES  ========================================= --

/-- At every stored ambient type whose real image has coordinates, so a float
interval matrix is an instance too. The operation instances below are stated
only at `Vec`, which is where an algorithm asks for them. -/
instance {α β ι : Type} [RealImage α β] [AddCommGroup β] [Module ℝ β] [Entrywise β ι] :
    ContSet (Interval α) β := ⟨Interval.construct⟩

instance {α β ι : Type} [RealImage α β] [AddCommGroup β] [Module ℝ β] [Entrywise β ι] :
    ConvexSet (Interval α) β := ⟨fun I => I.nominal.convex_construct⟩

/-- At `Vec` alone, as over ℝ: the norm compactness bounds is not read
coordinatewise. -/
instance : CompactSet (Interval (Vec 𝕋 n)) (Vec ℝ n) := ⟨Interval.isCompact_construct⟩

instance : Plus (Interval (Vec 𝕋 n)) (Vec ℝ n) where
  plus I₁ I₂ := (Interval.plus I₁ I₂).materialise
  plus_outer I₁ I₂ := by
    rw [Interval.materialise_eq]
    exact Interval.plus_outer I₁ I₂

instance : MinkDiff (Interval (Vec 𝕋 n)) (Vec ℝ n) where
  minkDiff I₁ I₂ := (Interval.minkDiff I₁ I₂).materialise
  minkDiff_inner I₁ I₂ := by
    rw [Interval.materialise_eq]
    exact Interval.minkDiff_inner I₁ I₂

instance : Intersection (Interval (Vec 𝕋 n)) (Vec ℝ n) where
  intersection := Interval.intersection
  intersection_outer I₁ I₂ := (Interval.intersection_exact I₁ I₂).symm.subset

instance : LinComb (Interval (Vec 𝕋 n)) (Vec ℝ n) where
  linComb I₁ I₂ := (Interval.linComb I₁ I₂).materialise
  linComb_outer I₁ I₂ := by
    rw [Interval.materialise_eq]
    exact Interval.linComb_outer I₁ I₂

/-- Nothing to reduce — a box is its own order — so this is storage and no more,
which is exactly what a loop calling `reduce` every step wants of it. -/
instance : Reduce (Interval (Vec 𝕋 n)) (Vec ℝ n) where
  reduce I _ := I.materialise
  reduce_outer I _ := by
    rw [Interval.materialise_eq]

/-- The one field here that is an equality: a relabelling does no arithmetic, so
the float box loses exactly what the exact one does, namely nothing. -/
instance : Reindex (fun n => Interval (Vec 𝕋 n)) where
  reindex e I := (Interval.reindex e I).materialise
  reindex_exact e I := by
    rw [Interval.materialise_eq]
    exact Interval.reindex_exact e I

instance : Mtimes (Mat 𝕋) (fun n => Interval (Vec 𝕋 n)) where
  mtimes M I := (Interval.mtimes M I).materialise
  mtimes_outer M I := by
    simp only [ContSet.construct_mat, Set.biUnion_singleton, Interval.materialise_eq]
    exact Interval.mtimes_outer M I

/-- The same operation at an interval matrix, which the float `expIntervalTaylor`
chain builds towards: a box needs no fresh generator to absorb the rounding.
No scoped `ℐ` here, unlike `Real`'s: it would have to close over `𝕋`. -/
instance : Mtimes (fun m n => Interval (Mat 𝕋 m n)) (fun n => Interval (Vec 𝕋 n)) where
  mtimes IM I := (Interval.mtimesIntervalMat IM I).materialise
  mtimes_outer IM I := by
    rw [Interval.materialise_eq]
    exact Interval.mtimesIntervalMat_outer IM I

/-- A zero-width box at the stored point, nothing rounded. -/
instance : OfScalarPoint 𝕋 (fun n => Interval (Vec 𝕋 n)) where
  ofVec v := Interval.point v
  mem_ofVec v := Interval.mem_point v

/-- The rounded midpoint: any point of the box would do, as `enlarge` is sound about any. -/
instance : ScalarCentre 𝕋 (fun n => Interval (Vec 𝕋 n)) where
  centreVec I := Interval.center I

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

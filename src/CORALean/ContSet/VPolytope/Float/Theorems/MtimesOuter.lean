import CORALean.ContSet.InflatedContSet.Theorems.MapSubset
import CORALean.ContSet.Interval.Float.Theorems.MtimesOuter
import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
import CORALean.ContSet.Interval.Real.Theorems.Convex
import CORALean.ContSet.VPolytope.Float.Operations.ColumnGap
import CORALean.ContSet.VPolytope.Float.Operations.MemColumnGap
import CORALean.ContSet.VPolytope.Float.Operations.Mtimes
import CORALean.ContSet.VPolytope.Real.Theorems.MtimesExact

/-!
# `VPolytope.mtimes` over-approximates the image under a linear map

`InflatedContSet.map_subset` splits this in two. The nominal obligation is the
exact `mtimes_exact` — the image of a hull is the hull of the images — followed
by `construct_subset_add`, every stored column being within `columnGap` of the
exact product. The error obligation is the interval `mtimes` and one `plus`.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open Matrix Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}

theorem VPolytope.aux_mtimes_nominal (M : Mat 𝕋 m n) (P : VPolytope 𝕋 n) :
    (toRealMat M *ᵥ ·) '' nominalSet P ⊆
      nominalSet (VPolytope.mtimes M P)
        + (VPolytope.columnGap (matMulDown M P.V) (matMulUp M P.V)).construct := by
  have hexact : (toRealMat M *ᵥ ·) '' nominalSet P
      = (Real.VPolytope.mtimes (toRealMat M) (nominal P)).construct :=
    Real.VPolytope.mtimes_exact _ _
  rw [hexact]
  refine Real.VPolytope.construct_subset_add _ _ (Real.Interval.convex_construct _) fun l => ?_
  exact VPolytope.mem_columnGap fun i => ⟨dotDown_le _ _, le_dotUp _ _⟩

-- the old box travels through the map and absorbs the column gap on the way
theorem VPolytope.aux_mtimes_error (M : Mat 𝕋 m n) (P : VPolytope 𝕋 n) :
    (toRealMat M *ᵥ ·) '' (error P).construct
      + (VPolytope.columnGap (matMulDown M P.V) (matMulUp M P.V)).construct ⊆
      (error (VPolytope.mtimes M P)).construct :=
  subset_trans (Set.add_subset_add_right (Interval.mtimes_outer M P.E))
    (Interval.plus_outer _ _)

theorem VPolytope.mtimes_outer (M : Mat 𝕋 m n) (P : VPolytope 𝕋 n) :
    (toRealMat M *ᵥ ·) '' P.construct ⊆ (VPolytope.mtimes M P).construct :=
  map_subset (fun x y => Matrix.mulVec_add _ x y)
    (VPolytope.aux_mtimes_nominal M P) (VPolytope.aux_mtimes_error M P)

end CORALean.Float

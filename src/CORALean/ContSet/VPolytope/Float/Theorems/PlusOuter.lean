import CORALean.ContSet.InflatedContSet.Theorems.PlusSubset
import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
import CORALean.ContSet.Interval.Real.Theorems.Convex
import CORALean.ContSet.VPolytope.Float.Operations.ColumnGap
import CORALean.ContSet.VPolytope.Float.Operations.MemColumnGap
import CORALean.ContSet.VPolytope.Float.Operations.PairSum
import CORALean.ContSet.VPolytope.Float.Operations.Plus

/-!
# `VPolytope.plus` over-approximates the Minkowski sum

`InflatedContSet.plus_subset` splits this in two. The nominal obligation is the
exact `plus_exact` — which makes the sum of the two hulls the hull of the
pairwise sums — followed by `construct_subset_add`, since every stored vertex is
within `columnGap` of the exact one. The error obligation is two applications of
`Interval.plus_outer`.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

/-- The stored vertices differ from the exact pairwise sums by no more than the
gap between the two roundings. -/
theorem VPolytope.aux_plus_nominal (P₁ P₂ : VPolytope 𝕋 n) :
    nominalSet P₁ + nominalSet P₂ ⊆
      nominalSet (P₁.plus P₂) + (VPolytope.columnGap
        (VPolytope.pairSum addDown P₁ P₂) (VPolytope.pairSum addUp P₁ P₂)).construct := by
  have hexact : nominalSet P₁ + nominalSet P₂
      = ((nominal P₁).plus (nominal P₂)).construct :=
    Real.VPolytope.plus_exact _ _
  rw [hexact]
  refine Real.VPolytope.construct_subset_add _ _ (Real.Interval.convex_construct _) fun l => ?_
  exact VPolytope.mem_columnGap fun i => ⟨addDown_le_add _ _, add_le_addUp _ _⟩

-- the box absorbs the two incoming boxes and that pairwise-sum gap
theorem VPolytope.aux_plus_error (P₁ P₂ : VPolytope 𝕋 n) :
    (error P₁).construct + (error P₂).construct
      + (VPolytope.columnGap (VPolytope.pairSum addDown P₁ P₂)
          (VPolytope.pairSum addUp P₁ P₂)).construct ⊆ (error (P₁.plus P₂)).construct :=
  subset_trans (Set.add_subset_add_right (Interval.plus_outer P₁.E P₂.E))
    (Interval.plus_outer _ _)

theorem VPolytope.plus_outer (P₁ P₂ : VPolytope 𝕋 n) :
    P₁.construct + P₂.construct ⊆ (P₁.plus P₂).construct :=
  InflatedContSet.plus_subset (VPolytope.aux_plus_nominal P₁ P₂)
    (VPolytope.aux_plus_error P₁ P₂)

end CORALean.Float

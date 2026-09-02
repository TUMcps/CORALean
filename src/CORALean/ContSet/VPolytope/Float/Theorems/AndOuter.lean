import CORALean.ContSet.VPolytope.Float.Operations.And
import CORALean.ContSet.VPolytope.Float.Theorems.IntervalOuter

/-!
# The float `VPolytope.and` contains the intersection

The same three steps as the exact layer's, each already proved here.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

theorem VPolytope.and_outer (P₁ P₂ : VPolytope 𝕋 n) :
    P₁.construct ∩ P₂.construct ⊆ (P₁.and P₂).construct := by
  refine subset_trans ?_ (VPolytope.subset_ofInterval _)
  rw [Interval.and_exact]
  exact Set.inter_subset_inter P₁.interval_outer P₂.interval_outer

end CORALean.Float

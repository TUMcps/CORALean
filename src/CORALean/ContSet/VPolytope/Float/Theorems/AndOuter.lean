import CORALean.ContSet.Conversion.Float.Interval_to_VPolytope
import CORALean.ContSet.Conversion.Float.VPolytope_to_Interval
import CORALean.ContSet.Interval.Float.Operations.And
import CORALean.ContSet.Interval.Float.Operations.AndExact
import CORALean.ContSet.VPolytope.Float.Operations.And

/-!
# The float `VPolytope.and` contains the intersection

The same three steps as the exact layer's, each already proved here.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem VPolytope.and_outer (P₁ P₂ : VPolytope 𝕋 n) :
    P₁.construct ∩ P₂.construct ⊆ (P₁.and P₂).construct := by
  refine subset_trans ?_ (Interval.vPolytope_contains _)
  rw [Interval.and_exact]
  exact Set.inter_subset_inter P₁.interval_contains P₂.interval_contains

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

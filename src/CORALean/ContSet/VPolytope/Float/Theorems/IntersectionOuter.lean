module

public import CORALean.ContSet.Conversion.Float.Interval_to_VPolytope
public import CORALean.ContSet.Conversion.Float.VPolytope_to_Interval
public import CORALean.ContSet.Interval.Float.Operations.Intersection
public import CORALean.ContSet.Interval.Float.Operations.IntersectionExact
public import CORALean.ContSet.VPolytope.Float.Operations.Intersection

@[expose] public section

/-!
# The float `VPolytope.intersection` contains the intersection

The same three steps as the exact layer's, each already proved here.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem VPolytope.intersection_outer (P₁ P₂ : VPolytope (Vec 𝕋 n)) :
    P₁.construct ∩ P₂.construct ⊆ (P₁.intersection P₂).construct := by
  refine subset_trans ?_ (Interval.vPolytope_contains _)
  rw [Interval.intersection_exact]
  exact Set.inter_subset_inter P₁.interval_contains P₂.interval_contains

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.ContSet.Conversion.Float.Theorems.IntervalVPolytopeContains
public import CORALean.ContSet.Conversion.Float.Theorems.Basic
public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.Interval.Float.Theorems.IntersectionExact
public import CORALean.ContSet.VPolytope.Float.Operations.Intersection
public import CORALean.ContSet.Conversion.Real.Theorems.HPolytopeIntervalContains
public import CORALean.ContSet.Conversion.Real.Theorems.HPolytopeVPolytopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.IntervalVPolytopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.VPolytopeIntervalContains

@[expose] public section

/-!
# The float `VPolytope.intersection` contains the intersection

The same three steps as the exact layer's, each already proved here.

## Inputs
* `P₁` – first polytope
* `P₂` – second polytope

## Hypotheses
* none

## Conclusion
* the intersection lies in the result
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      14-October-2026 (Tobias Ladner)


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

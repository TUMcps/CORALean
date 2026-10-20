module

public import CORALean.ContSet.HPolytope.Float.Theorems.ContractBoxOuter
public import CORALean.ContSet.VPolytope.Float.Operations.IntersectionCut
public import CORALean.ContSet.Interval.Float.Operations.IntersectionExact
public import CORALean.ContSet.Conversion.Float.Theorems.Basic
public import CORALean.ContSet.Conversion.Float.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_HPolytope
public import CORALean.ContSet.Conversion.Real.Operations.Basic
public import CORALean.ContSet.Conversion.Float.Theorems.IntervalVPolytopeContains
public import CORALean.ContSet.Conversion.Float.Theorems.VPolytopeHPolytopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.HPolytopeIntervalContains
public import CORALean.ContSet.Conversion.Real.Theorems.HPolytopeVPolytopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.IntervalVPolytopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.VPolytopeHPolytopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.VPolytopeIntervalContains
public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopeIntervalContains

@[expose] public section

/-!
# The float `VPolytope.intersectionCut` contains the intersection

A point of both operands lies in both boxes, hence in their intersection, and in both
halfspace descriptions, which the cuts keep it through one after the other.

## Inputs
* `P₁` – first polytope
* `P₂` – second polytope
* `Aq₁` – cut directions of the first operand
* `Aq₂` – cut directions of the second operand

## Hypotheses
* none

## Conclusion
* the intersection lies in the result
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n q₁ q₂ : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem VPolytope.intersectionCut_outer (P₁ P₂ : VPolytope (Vec 𝕋 n)) (Aq₁ : Mat 𝕋 q₁ n)
    (Aq₂ : Mat 𝕋 q₂ n) : -- --- CONCL ---
    P₁.construct ∩ P₂.construct ⊆ (P₁.intersectionCut P₂ Aq₁ Aq₂).construct := by -- --- PROOF ---
  rintro x ⟨h₁, h₂⟩
  refine Interval.vPolytope_contains _ ?_
  refine (P₂.hPolytope Aq₂).contractBox_outer _ ⟨?_, P₂.hPolytope_contains Aq₂ h₂⟩
  refine (P₁.hPolytope Aq₁).contractBox_outer _ ⟨?_, P₁.hPolytope_contains Aq₁ h₁⟩
  rw [Interval.intersection_exact]
  exact ⟨P₁.interval_contains h₁, P₂.interval_contains h₂⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

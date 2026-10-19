module

public import CORALean.ContSet.Conversion.Real.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_HPolytope
public import CORALean.ContSet.HPolytope.Real.Theorems.IntersectionExact

@[expose] public section

/-!
# `VPolytope.intersectionH`

Intersection is the operation vertices are worst at, so it goes out to
halfspaces, where intersection is free: the two operands, on the caller's
directions, and one operand's own box, so the result is bounded.

## Inputs
* `P₁` – first polytope
* `P₂` – second polytope
* `Aq₁` – cut directions of the first operand
* `Aq₂` – cut directions of the second operand

## Output
* halfspace polytope of the intersection
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n q₁ q₂ : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The intersection as halfspaces, kept bounded by one operand's own box. -/
noncomputable def VPolytope.intersectionH (P₁ P₂ : VPolytope (Vec ℝ n))
    (Aq₁ : Fin q₁ → (Vec ℝ n →ₗ[ℝ] ℝ)) (Aq₂ : Fin q₂ → (Vec ℝ n →ₗ[ℝ] ℝ)) :
    HPolytope (Vec ℝ n) :=
  ((P₁.hPolytope Aq₁).intersection (P₂.hPolytope Aq₂)).intersection (Interval.hPolytope P₁.interval)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

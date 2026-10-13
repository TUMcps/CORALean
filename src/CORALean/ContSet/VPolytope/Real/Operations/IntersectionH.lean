import CORALean.ContSet.Conversion.Real.VPolytope_to_HPolytope
import CORALean.ContSet.Conversion.Real.Interval_to_HPolytope
import CORALean.ContSet.Conversion.Real.VPolytope_to_Interval
import CORALean.ContSet.HPolytope.Real.Theorems.IntersectionExact

/-!
# `VPolytope.intersectionH`

Intersection is the operation vertices are worst at, so it goes out to
halfspaces, where intersection is free: the two operands, on the caller's
directions, and one operand's own box, so the result is bounded.
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

module

public import CORALean.ContSet.Conversion.Real.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Theorems.Basic
public import CORALean.ContSet.Conversion.Real.Theorems.HPolytopeVPolytopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.IntervalHPolytopeExact
public import CORALean.ContSet.HPolytope.Real.Theorems.IntersectionExact
public import CORALean.ContSet.VPolytope.Real.Operations.IntersectionH
public import CORALean.ContSet.Conversion.Real.Operations.HPolytope_to_VPolytope
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_VPolytope
public import CORALean.ContSet.Conversion.Real.Theorems.IntervalVPolytopeContains

@[expose] public section

/-!
# `VPolytope.intersectionH` is compact

The halfspace description sits inside one operand's own box, which a vertex
description already knows is compact.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n q₁ q₂ : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem VPolytope.intersectionH_isCompact (P₁ P₂ : VPolytope (Vec ℝ n))
    (Aq₁ : Fin q₁ → (Vec ℝ n →ₗ[ℝ] ℝ)) (Aq₂ : Fin q₂ → (Vec ℝ n →ₗ[ℝ] ℝ)) :
    IsCompact (VPolytope.intersectionH P₁ P₂ Aq₁ Aq₂).construct := by
  refine HPolytope.isCompact_of_contains (W := P₁.interval.vPolytope) fun x hx => ?_
  have h := (HPolytope.mem_intersection_iff.mp hx).2
  rw [Interval.hPolytope_exact] at h
  exact Interval.vPolytope_contains _ h

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

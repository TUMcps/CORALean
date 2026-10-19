module

public import CORALean.ContSet.VPolytope.Real.Operations.IntersectionH
public import CORALean.ContSet.VPolytope.Real.Operations.IntersectionHIsCompact
public import CORALean.ContSet.VPolytope.Real.Operations.EmptySet
public import CORALean.ContSet.Conversion.Real.Operations.HPolytope_to_VPolytope
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_VPolytope

@[expose] public section

/-!
# `VPolytope.intersection`

Intersection is the operation vertices are worst at — the result's vertices are generally none of
either operand's — so it goes out to halfspaces, where intersection is free, and comes back: out on
directions the caller names, back by exact vertex enumeration. So `intersection` is exact whenever
the directions contain each operand's facet normals, and merely encloses otherwise; the directions
are the whole of the imprecision. One extra row goes in on the way out, one operand's own box, so
that the halfspace description is bounded and can be converted back; it costs nothing. If the
halfspace description denotes nothing so does the intersection, and the answer is the empty vertex
list.

## Inputs
* `P₁` – first polytope
* `P₂` – second polytope
* `Aq₁` – cut directions of the first operand
* `Aq₂` – cut directions of the second operand

## Output
* vertices of the halfspace intersection
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open scoped Classical

variable {n q₁ q₂ : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def VPolytope.intersection (P₁ P₂ : VPolytope (Vec ℝ n))
    (Aq₁ : Fin q₁ → (Vec ℝ n →ₗ[ℝ] ℝ)) (Aq₂ : Fin q₂ → (Vec ℝ n →ₗ[ℝ] ℝ)) :
    VPolytope (Vec ℝ n) :=
  if h : (VPolytope.intersectionH P₁ P₂ Aq₁ Aq₂).construct.Nonempty then
    (VPolytope.intersectionH P₁ P₂ Aq₁ Aq₂).vPolytope h
  else VPolytope.emptySet _

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

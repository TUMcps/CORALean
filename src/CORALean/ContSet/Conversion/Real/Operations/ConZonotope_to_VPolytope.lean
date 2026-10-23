module

public import CORALean.ContSet.ConZonotope.Real.Operations.Domain
public import CORALean.ContSet.ConZonotope.Real.Theorems.MemDomainIff
public import CORALean.ContSet.ConZonotope.Real.Theorems.Convex
public import CORALean.ContSet.ConZonotope.Real.Theorems.IsCompactDomain
public import CORALean.ContSet.Conversion.Real.Operations.HPolytope_to_VPolytope
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_VPolytope

@[expose] public section

/-!
# A constrained zonotope as its vertices

## Inputs
* `cZ` – constrained zonotope

## Hypotheses
* `hne` – domain is nonempty

## Output
* vertex polytope of the constrained zonotope
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def ConZonotope.vPolytope (cZ : ConZonotope α)
    (hne : cZ.domain.construct.Nonempty) : VPolytope α where
  k := (cZ.domain.vPolytope hne).k
  V := fun l => cZ.c + ∑ j, ((cZ.domain.vPolytope hne).V l) j • cZ.G j

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.ContSet.Conversion.Real.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Theorems.ConZonotopeConPolyZonoExact
public import CORALean.ContSet.Conversion.Real.Theorems.VPolytopeConZonotopeExact

@[expose] public section

/-!
# A hull as a constrained polynomial zonotope

CORA's `conPolyZono(conZonotope(P))`: the hull's constrained zonotope is exact
(`VPolytope.conZonotope_exact`), and so is its reading as a constrained polynomial zonotope
(`ConZonotope.conPolyZono_exact`), so the conversion is the hull itself.

## Inputs
* `P` – vertex polytope

## Hypotheses
* none

## Conclusion
* polytope is contained in its constrained polynomial zonotope
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       06-September-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem VPolytope.conPolyZono_contains (P : VPolytope (Vec ℝ n)) :
    P.construct ⊆ P.conPolyZono.construct :=
  ((VPolytope.conZonotope_exact P).trans (ConZonotope.conPolyZono_exact _)).subset

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

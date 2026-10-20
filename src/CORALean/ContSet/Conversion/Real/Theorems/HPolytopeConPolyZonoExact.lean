module

public import CORALean.ContSet.Conversion.Real.Operations.HPolytope_to_ConPolyZono
public import CORALean.ContSet.Conversion.Real.Theorems.ConZonotopeConPolyZonoExact
public import CORALean.ContSet.Conversion.Real.Theorems.HPolytopeConZonotopeExact

@[expose] public section

/-!
# CORA's `conPolyZono(P)` is the polytope

Both steps are exact: `HPolytope.conZonotope_exact` and `ConZonotope.conPolyZono_exact`.

## Inputs
* `up` – certified upper bound per coordinate
* `lo` – certified lower bound per coordinate

## Hypotheses
* none

## Conclusion
* constrained polynomial zonotope equals the polytope
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ} {P : HPolytope (Vec ℝ n)}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `conPolyZono(conZonotope(P))` denotes `P`. -/
theorem HPolytope.conPolyZono_exact (up : ∀ j, SupportBound P.construct (LinearMap.proj j))
    (lo : ∀ j, SupportBound P.construct (-LinearMap.proj j)) :
    (HPolytope.conPolyZono up lo).construct = P.construct :=
  (ConZonotope.conPolyZono_exact _).symm.trans (HPolytope.conZonotope_exact up lo)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

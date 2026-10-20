module

public import CORALean.ContSet.Conversion.Real.Theorems.ZonoBundleZonotopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopeVPolytopeContains
public import CORALean.ContSet.Conversion.Real.Operations.ZonoBundle_to_ConZonotope
public import CORALean.ContSet.Conversion.Real.Theorems.ConZonotopeVPolytopeContains
public import CORALean.ContSet.Conversion.Real.Operations.ZonoBundle_to_VPolytope
public import CORALean.ContSet.Conversion.Real.Operations.ConZonotope_to_VPolytope
public import CORALean.ContSet.Conversion.Real.Operations.HPolytope_to_VPolytope
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_VPolytope
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_VPolytope
public import CORALean.ContSet.Conversion.Real.Theorems.HPolytopeVPolytopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.IntervalVPolytopeContains

@[expose] public section

/-!
# A bundle's corners, at one component

Through `ZonoBundle.zonotope i`, then that zonotope's own `2ʰ` sign corners. Whichever component `i`
names throws away every other one the bundle intersects against; the corner step is exact, so all
the loss is the choice of component. `vPolytopeAll` keeps every member, as CORA's `vertices_` of a
bundle does (through `polytope(zB)`): the vertices of the exact `conZonotope(zB)`
(`conZonotopeAll`). It needs a nonempty bundle, where CORA returns an empty vertex list; the list
may hold interior points, but its hull is the bundle, which `vPolytopeAll_exact` proves.

## Inputs
* `zB` – zonotope bundle
* `i` – member index

## Hypotheses
* none

## Conclusion
* bundle is contained in its vertex polytope
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.vPolytope_contains (zB : ZonoBundle (Vec ℝ n)) (i : Fin zB.k) :
    zB.construct ⊆ (zB.vPolytope i).construct :=
  subset_trans (zB.zonotope_contains i) (Zonotope.vPolytope_contains _)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

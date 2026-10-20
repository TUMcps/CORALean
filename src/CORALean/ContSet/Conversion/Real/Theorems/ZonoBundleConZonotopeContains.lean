module

public import CORALean.ContSet.Conversion.Real.Theorems.ZonoBundleZonotopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopeConZonotopeExact
public import CORALean.ContSet.ConZonotope.Real.Theorems.ConstructFoldlIntersectionEq
public import CORALean.ContSet.Conversion.Real.Operations.ZonoBundle_to_ConZonotope
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_ConZonotope

@[expose] public section

/-!
# A bundle's constrained zonotope, at one component

Through `ZonoBundle.zonotope i`, then the constrained zonotope with nothing to satisfy, which loses
nothing. Whichever component `i` names throws away every other one the bundle intersects against, so
all the loss is that choice. `conZonotopeAll` keeps every member, as CORA's `conZonotope(zB)` does:
the first member's constrained zonotope, intersected one `ConZonotope.intersection` at a time with
each of the others. Exact over ℝ, as each intersection is, and it needs a first member, `0 < k`:
CORA answers `conZonotope.empty` for no members, where a bundle of none is the whole space here.

## Inputs
* `zB` – zonotope bundle
* `i` – member index

## Hypotheses
* none

## Conclusion
* bundle is contained in its constrained zonotope
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.conZonotope_contains (zB : ZonoBundle α) (i : Fin zB.k) :
    zB.construct ⊆ (zB.conZonotope i).construct :=
  subset_trans (zB.zonotope_contains i) (Zonotope.conZonotope_exact _).subset

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

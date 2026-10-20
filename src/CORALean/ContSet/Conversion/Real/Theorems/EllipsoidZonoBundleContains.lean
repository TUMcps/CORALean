module

public import CORALean.ContSet.Conversion.Real.Theorems.EllipsoidZonotopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopeZonoBundleExact
public import CORALean.ContSet.Conversion.Real.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Theorems.IntervalZonotopeContains

@[expose] public section

/-!
# An ellipsoid as a bundle of one

Through the ellipsoid's own box's zonotope, then `Zonotope.zonoBundle` — the
single-member bundle, exact by `Set.iInter_const`. All the loss is the box
route's, so this is no worse than `Ellipsoid → Zonotope` already is.

## Inputs
* `E` – ellipsoid

## Hypotheses
* none

## Conclusion
* ellipsoid is contained in its zonotope bundle
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.zonoBundle_contains (E : Ellipsoid n) :
    E.construct ⊆ E.zonoBundle.construct :=
  subset_trans E.zonotope_contains (Zonotope.zonoBundle_exact _).subset

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

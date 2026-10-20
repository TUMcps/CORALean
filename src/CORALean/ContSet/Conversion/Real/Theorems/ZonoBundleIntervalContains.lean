module

public import CORALean.ContSet.Conversion.Real.Theorems.ZonoBundleZonotopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopeIntervalContains
public import Mathlib.Order.BourbakiWitt
public import CORALean.ContSet.Conversion.Real.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval

@[expose] public section

/-!
# A bundle's box, at one component

Through `ZonoBundle.zonotope i`: the choice of component is free, and it already
throws away every other one the bundle intersects against — the whole point of
a bundle being that the intersection is tighter than any one member. The box
step then loses nothing further.

## Inputs
* `zB` – zonotope bundle
* `i` – member index

## Hypotheses
* none

## Conclusion
* bundle is contained in its interval
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      16-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.interval_contains (zB : ZonoBundle (Vec ℝ n)) (i : Fin zB.k) :
    zB.construct ⊆ (zB.interval i).construct :=
  subset_trans (zB.zonotope_contains i) (Zonotope.interval_contains _)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

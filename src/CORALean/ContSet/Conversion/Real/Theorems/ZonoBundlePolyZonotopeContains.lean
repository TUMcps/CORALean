module

public import CORALean.ContSet.Conversion.Real.Theorems.ZonoBundleZonotopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopePolyZonotopeExact
public import Mathlib.Order.BourbakiWitt
public import CORALean.ContSet.Conversion.Real.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_PolyZonotope

@[expose] public section

/-!
# A bundle's polynomial zonotope, at one component

Through `ZonoBundle.zonotope i`, then that zonotope's own exact reading as a
polynomial zonotope with one factor per generator. Whichever component `i`
names already throws away every other one the bundle intersects against — the
whole point of a bundle being that the intersection is tighter than any one
member — so all the loss here is that choice.

## Inputs
* `zB` – zonotope bundle
* `i` – member index

## Hypotheses
* none

## Conclusion
* bundle is contained in its polynomial zonotope
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.polyZonotope_contains (zB : ZonoBundle α) (i : Fin zB.k) :
    zB.construct ⊆ (zB.polyZonotope i).construct :=
  subset_trans (zB.zonotope_contains i) (Zonotope.polyZonotope_exact _).subset

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

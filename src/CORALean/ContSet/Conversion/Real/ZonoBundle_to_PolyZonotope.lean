import CORALean.ContSet.Conversion.Real.ZonoBundle_to_Zonotope
import CORALean.ContSet.Conversion.Real.Zonotope_to_PolyZonotope

/-!
# A bundle's polynomial zonotope, at one component

Through `ZonoBundle.zonotope i`, then that zonotope's own exact reading as a
polynomial zonotope with one factor per generator. Whichever component `i`
names already throws away every other one the bundle intersects against — the
whole point of a bundle being that the intersection is tighter than any one
member — so all the loss here is that choice.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]

def ZonoBundle.polyZonotope (zB : ZonoBundle α) (i : Fin zB.k) : PolyZonotope α :=
  (zB.zonotope i).polyZonotope


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.polyZonotope_contains (zB : ZonoBundle α) (i : Fin zB.k) :
    zB.construct ⊆ (zB.polyZonotope i).construct :=
  subset_trans (zB.zonotope_contains i) (Zonotope.polyZonotope_exact _).subset

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

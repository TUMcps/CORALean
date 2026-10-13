import CORALean.ContSet.Conversion.Real.ZonoBundle_to_Zonotope
import CORALean.ContSet.Conversion.Real.Zonotope_to_ConPolyZono
import Mathlib.Order.BourbakiWitt

/-!
# A bundle's constrained polynomial zonotope, at one component

Through `ZonoBundle.zonotope i`, then that zonotope's own exact reading as a
constrained polynomial zonotope with an empty constraint system. Whichever
component `i` names already throws away every other one the bundle intersects
against — the whole point of a bundle being that the intersection is tighter
than any one member — so all the loss here is that choice.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]

def ZonoBundle.conPolyZono (zB : ZonoBundle α) (i : Fin zB.k) : ConPolyZono α :=
  (zB.zonotope i).conPolyZono


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.conPolyZono_contains (zB : ZonoBundle α) (i : Fin zB.k) :
    zB.construct ⊆ (zB.conPolyZono i).construct :=
  subset_trans (zB.zonotope_contains i) (Zonotope.conPolyZono_exact _).subset

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

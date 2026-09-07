import CORALean.ContSet.Conversion.Real.ZonoBundle_to_Zonotope
import CORALean.ContSet.Conversion.Real.Zonotope_to_ConPolyZono

/-!
# A bundle's constrained polynomial zonotope, at one component

Through `ZonoBundle.zonotope i`, then that zonotope's own exact reading as a
constrained polynomial zonotope with an empty constraint system. Whichever
component `i` names already throws away every other one the bundle intersects
against — the whole point of a bundle being that the intersection is tighter
than any one member — so all the loss here is that choice.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]

def ZonoBundle.conPolyZono (B : ZonoBundle α) (i : Fin B.k) : ConPolyZono α :=
  (B.zonotope i).conPolyZono


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.subset_conPolyZono (B : ZonoBundle α) (i : Fin B.k) :
    B.construct ⊆ (B.conPolyZono i).construct :=
  subset_trans (B.subset_zonotope i) (Zonotope.conPolyZono_exact _).subset

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

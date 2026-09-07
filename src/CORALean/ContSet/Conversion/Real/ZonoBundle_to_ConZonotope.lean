import CORALean.ContSet.Conversion.Real.ZonoBundle_to_Zonotope
import CORALean.ContSet.Conversion.Real.Zonotope_to_ConZonotope

/-!
# A bundle's constrained zonotope, at one component

Through `ZonoBundle.zonotope i`, then the constrained zonotope with nothing to
satisfy — that second leg loses nothing. Whichever component `i` names already
throws away every other one the bundle intersects against — the whole point of
a bundle being that the intersection is tighter than any one member — so all the
loss here is that choice.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]

def ZonoBundle.conZonotope (zB : ZonoBundle α) (i : Fin zB.k) : ConZonotope α :=
  (zB.zonotope i).conZonotope


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.conZonotope_contains (zB : ZonoBundle α) (i : Fin zB.k) :
    zB.construct ⊆ (zB.conZonotope i).construct :=
  subset_trans (zB.zonotope_contains i) (Zonotope.conZonotope_exact _).subset

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

import CORALean.ContSet.Conversion.Real.ConZonotope_to_Zonotope
import CORALean.ContSet.Conversion.Real.Zonotope_to_PolyZonotope

/-!
# A constrained zonotope as a polynomial zonotope

Constraints dropped, then the plain zonotope's exact reading as a polynomial
zonotope with one factor per generator. Loses exactly the constraints thrown
away; a direct polynomial zonotope that used the constraints instead is a
separate piece of mathematics, and its dependent structure would go unused
here regardless.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]

def ConZonotope.polyZonotope (C : ConZonotope α) : PolyZonotope α :=
  C.zonotope.polyZonotope


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.subset_polyZonotope (C : ConZonotope α) :
    C.construct ⊆ C.polyZonotope.construct :=
  subset_trans C.zonotope_outer (Zonotope.polyZonotope_exact _).subset

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

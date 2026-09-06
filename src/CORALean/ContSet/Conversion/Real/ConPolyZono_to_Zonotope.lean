import CORALean.ContSet.Conversion.Real.ConPolyZono_to_PolyZonotope
import CORALean.ContSet.Conversion.Real.PolyZonotope_to_Zonotope

/-!
# A constrained polynomial zonotope as a zonotope

Through `ConPolyZono.polyZonotope`, then that polynomial zonotope's own zonotope.
A two-hop composition, and precision is lost twice: the constraints go first,
freeing every factor the equalities were confining to range over the whole cube,
and then the sharing goes, at `PolyZonotope.zonotope`, freeing every dependent
generator to move independently of the others. For a representation whose whole
point is the constraints, that is a lot to give up, and neither loss is
recovered by the other.

A direct zonotope from a constrained polynomial zonotope is a separate piece of
mathematics and no tighter enclosure is attempted here.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]

def ConPolyZono.zonotope (C : ConPolyZono α) : Zonotope α :=
  C.polyZonotope.zonotope


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.zonotope_outer (C : ConPolyZono α) :
    C.construct ⊆ C.zonotope.construct :=
  subset_trans C.polyZonotope_outer (PolyZonotope.zonotope_outer _)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

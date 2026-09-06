import CORALean.ContSet.Conversion.Real.ConPolyZono_to_PolyZonotope
import CORALean.ContSet.Conversion.Real.PolyZonotope_to_ConZonotope

/-!
# A constrained polynomial zonotope as a constrained zonotope

Through `ConPolyZono.polyZonotope`, then that polynomial zonotope's own
constrained zonotope — a constrained zonotope with nothing to satisfy, that
second leg being exact. A two-hop composition, and precision is still lost
twice: the constraints go first, freeing every factor the equalities were
confining, and then the sharing goes, at `PolyZonotope.zonotope`. For a
representation whose whole point is the constraints, that is a lot to give up,
and neither loss is recovered by the other.

A direct constrained zonotope carrying the original constraints is a separate
piece of mathematics and no tighter enclosure is attempted here.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]

def ConPolyZono.conZonotope (C : ConPolyZono α) : ConZonotope α :=
  C.polyZonotope.conZonotope


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.subset_conZonotope (C : ConPolyZono α) :
    C.construct ⊆ C.conZonotope.construct :=
  subset_trans C.polyZonotope_outer (PolyZonotope.subset_conZonotope _)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

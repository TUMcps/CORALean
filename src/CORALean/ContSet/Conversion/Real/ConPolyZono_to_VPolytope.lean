import CORALean.ContSet.Conversion.Real.ConPolyZono_to_PolyZonotope
import CORALean.ContSet.Conversion.Real.PolyZonotope_to_VPolytope

/-!
# A constrained polynomial zonotope as its corners

Through `ConPolyZono.polyZonotope`, then that polynomial zonotope's own corners.
A two-hop composition, and precision is lost twice: the constraints go first,
freeing every factor the equalities were confining, and then the sharing goes,
at `PolyZonotope.zonotope`, before the corner step, itself exact, is taken. For a
representation whose whole point is the constraints, that is a lot to give up,
and neither loss is recovered by the other.

A direct vertex hull from a constrained polynomial zonotope is a separate piece
of mathematics and no tighter enclosure is attempted here.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]

noncomputable def ConPolyZono.vPolytope (C : ConPolyZono α) : VPolytope α :=
  C.polyZonotope.vPolytope


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.subset_vPolytope (C : ConPolyZono α) :
    C.construct ⊆ C.vPolytope.construct :=
  subset_trans C.polyZonotope_outer (PolyZonotope.subset_vPolytope _)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

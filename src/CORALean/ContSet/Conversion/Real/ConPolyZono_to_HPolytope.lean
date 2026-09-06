import CORALean.ContSet.Conversion.Real.ConPolyZono_to_PolyZonotope
import CORALean.ContSet.Conversion.Real.PolyZonotope_to_HPolytope

/-!
# A constrained polynomial zonotope as halfspaces

Through `ConPolyZono.polyZonotope`, then that polynomial zonotope's own halfspace
description. A two-hop composition, and precision is lost twice: the constraints
go first, freeing every factor the equalities were confining, and then the
sharing goes, at `PolyZonotope.zonotope`, before the caller's rows are read off
the result. For a representation whose whole point is the constraints, that is a
lot to give up, and neither loss is recovered by the other.

A direct halfspace description from a constrained polynomial zonotope is a
separate piece of mathematics and no tighter enclosure is attempted here.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α] {q : ℕ}

noncomputable def ConPolyZono.hPolytope (C : ConPolyZono α) (Aq : Fin q → (α →ₗ[ℝ] ℝ)) :
    HPolytope α :=
  C.polyZonotope.hPolytope Aq


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.subset_hPolytope (C : ConPolyZono α) (Aq : Fin q → (α →ₗ[ℝ] ℝ)) :
    C.construct ⊆ (C.hPolytope Aq).construct :=
  subset_trans C.polyZonotope_outer (PolyZonotope.subset_hPolytope _ _)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

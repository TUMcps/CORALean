module

public import CORALean.ContSet.Conversion.Real.ConPolyZono_to_PolyZonotope
public import CORALean.ContSet.Conversion.Real.PolyZonotope_to_HPolytope
public import CORALean.ContSet.Conversion.Real.Operations.ConPolyZono_to_HPolytope

@[expose] public section

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

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α] {qI : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.hPolytope_contains (cPZ : ConPolyZono α) (Aq : Fin qI → (α →ₗ[ℝ] ℝ)) :
    cPZ.construct ⊆ (cPZ.hPolytope Aq).construct :=
  subset_trans cPZ.polyZonotope_contains (PolyZonotope.hPolytope_contains _ _)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

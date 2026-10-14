module

public import CORALean.ContSet.Conversion.Real.Theorems.ConPolyZonoPolyZonotopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.Basic
public import CORALean.ContSet.Conversion.Real.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.PolyZonotope_to_VPolytope
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_VPolytope
public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopeVPolytopeContains

@[expose] public section

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

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.vPolytope_contains (cPZ : ConPolyZono α) :
    cPZ.construct ⊆ cPZ.vPolytope.construct :=
  subset_trans cPZ.polyZonotope_contains (PolyZonotope.vPolytope_contains _)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

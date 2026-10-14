module

public import CORALean.ContSet.Conversion.Real.ConPolyZono_to_PolyZonotope
public import CORALean.ContSet.Conversion.Real.PolyZonotope_to_Interval
public import CORALean.ContSet.Conversion.Real.Operations.ConPolyZono_to_Interval

@[expose] public section

/-!
# A constrained polynomial zonotope as a box

Through `ConPolyZono.polyZonotope`, then that polynomial zonotope's own box. A
two-hop composition, and precision is lost twice: the constraints go first,
freeing every factor the equalities were confining, and then the sharing goes,
at `PolyZonotope.zonotope`, before the box is read off the result. For a
representation whose whole point is the constraints, that is a lot to give up,
and neither loss is recovered by the other.

A direct box from a constrained polynomial zonotope is a separate piece of
mathematics and no tighter enclosure is attempted here.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.interval_contains (cPZ : ConPolyZono (Vec ℝ n)) :
    cPZ.construct ⊆ cPZ.interval.construct :=
  subset_trans cPZ.polyZonotope_contains (PolyZonotope.interval_contains _)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

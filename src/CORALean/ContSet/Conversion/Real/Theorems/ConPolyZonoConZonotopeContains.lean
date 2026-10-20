module

public import CORALean.ContSet.Conversion.Real.Theorems.ConPolyZonoPolyZonotopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.PolyZonotopeConZonotopeContains
public import CORALean.ContSet.Conversion.Real.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_ConZonotope

@[expose] public section

/-!
# A constrained polynomial zonotope as a constrained zonotope

Through `ConPolyZono.polyZonotope`, then that polynomial zonotope's own constrained zonotope, the
second leg exact. Precision is lost twice: the constraints go first, freeing every factor the
equalities were confining, and then the sharing goes, at `PolyZonotope.zonotope`. Neither loss is
recovered by the other. A direct constrained zonotope carrying the original constraints is a
separate piece of mathematics, and no tighter enclosure is attempted here.

## Inputs
* `cPZ` – constrained polynomial zonotope

## Hypotheses
* none

## Conclusion
* set is contained in its constrained zonotope
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.conZonotope_contains (cPZ : ConPolyZono α) :
    cPZ.construct ⊆ cPZ.conZonotope.construct :=
  subset_trans cPZ.polyZonotope_contains (PolyZonotope.conZonotope_contains _)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.ContSet.Conversion.Real.Theorems.ConPolyZonoPolyZonotopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.PolyZonotopeHPolytopeContains
public import CORALean.ContSet.Conversion.Real.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopeHPolytopeContains

@[expose] public section

/-!
# A constrained polynomial zonotope as halfspaces

Through `ConPolyZono.polyZonotope`, then that polynomial zonotope's own halfspace description.
Precision is lost twice: the constraints go first, freeing every factor the equalities were
confining, and then the sharing goes, at `PolyZonotope.zonotope`, before the caller's rows are read
off the result. Neither loss is recovered by the other. A direct halfspace description is a separate
piece of mathematics, and no tighter enclosure is attempted here.

## Inputs
* `cPZ` – constrained polynomial zonotope
* `Aq` – direction functionals

## Hypotheses
* none

## Conclusion
* set is contained in its halfspace polytope
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

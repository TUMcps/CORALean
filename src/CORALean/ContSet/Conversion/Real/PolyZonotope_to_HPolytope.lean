module

public import CORALean.ContSet.Conversion.Real.PolyZonotope_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Zonotope_to_HPolytope
public import CORALean.ContSet.Conversion.Real.Operations.PolyZonotope_to_HPolytope

@[expose] public section

/-!
# A polynomial zonotope as halfspaces

Through the zonotope enclosure, then that zonotope's own support bounds. A
polynomial zonotope's set is generally not even convex, so no halfspace
description is exact for it: this is an enclosure with a precision knob rather
than a conversion, and a direct construction would be tighter.

Loses whatever the zonotope step lost and nothing further; the rows are the
caller's, exactly as in `Zonotope.hPolytope_contains`.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α] {q : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.hPolytope_contains (pZ : PolyZonotope α) (Aq : Fin q → (α →ₗ[ℝ] ℝ)) :
    pZ.construct ⊆ (pZ.hPolytope Aq).construct :=
  subset_trans pZ.zonotope_contains (Zonotope.hPolytope_contains _ _)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

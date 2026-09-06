import CORALean.ContSet.Conversion.Real.PolyZonotope_to_Zonotope
import CORALean.ContSet.Conversion.Real.Zonotope_to_HPolytope

/-!
# A polynomial zonotope as halfspaces

Through the zonotope enclosure, then that zonotope's own support bounds. A
polynomial zonotope's set is generally not even convex, so no halfspace
description is exact for it: this is an enclosure with a precision knob rather
than a conversion, and a direct construction would be tighter.

Loses whatever the zonotope step lost and nothing further; the rows are the
caller's, exactly as in `Zonotope.subset_hPolytope`.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α] {q : ℕ}

def PolyZonotope.hPolytope (PZ : PolyZonotope α) (Aq : Fin q → (α →ₗ[ℝ] ℝ)) : HPolytope α :=
  PZ.zonotope.hPolytope Aq


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.subset_hPolytope (PZ : PolyZonotope α) (Aq : Fin q → (α →ₗ[ℝ] ℝ)) :
    PZ.construct ⊆ (PZ.hPolytope Aq).construct :=
  subset_trans PZ.zonotope_outer (Zonotope.subset_hPolytope _ _)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

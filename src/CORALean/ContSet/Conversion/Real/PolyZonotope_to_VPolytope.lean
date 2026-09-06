import CORALean.ContSet.Conversion.Real.PolyZonotope_to_Zonotope
import CORALean.ContSet.Conversion.Real.Zonotope_to_VPolytope

/-!
# A polynomial zonotope as its corners

Through the zonotope enclosure, then that zonotope's `2^h` sign corners. A
polynomial zonotope's set is generally not even convex, so no vertex hull is
exact for it: this is an enclosure with a precision knob rather than a
conversion, and a direct construction would be tighter.

Loses whatever the zonotope step lost and nothing further, the corner step
itself being exact.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]

noncomputable def PolyZonotope.vPolytope (PZ : PolyZonotope α) : VPolytope α :=
  PZ.zonotope.vPolytope


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.subset_vPolytope (PZ : PolyZonotope α) :
    PZ.construct ⊆ PZ.vPolytope.construct :=
  subset_trans PZ.zonotope_outer (Zonotope.subset_vPolytope _)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

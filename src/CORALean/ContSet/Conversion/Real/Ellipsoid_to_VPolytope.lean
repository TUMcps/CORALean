module

public import CORALean.ContSet.Conversion.Real.Ellipsoid_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Zonotope_to_VPolytope

@[expose] public section

/-!
# An ellipsoid as its corners

Through the zonotope, then that zonotope's `2^h` sign corners. A tight vertex
enclosure of an ellipsoid is its own fitting problem, not this composition, and
CORA leaves that choice to the caller too.

Loses whatever the zonotope step lost and nothing further, the corner step
being exact.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}

noncomputable def Ellipsoid.vPolytope (E : Ellipsoid n) : VPolytope (Vec ℝ n) :=
  E.zonotope.vPolytope


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.vPolytope_contains (E : Ellipsoid n) : E.construct ⊆ E.vPolytope.construct :=
  subset_trans E.zonotope_contains (Zonotope.vPolytope_contains _)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

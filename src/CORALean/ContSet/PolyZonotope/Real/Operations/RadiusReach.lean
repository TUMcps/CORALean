import CORALean.ContSet.Conversion.Real.PolyZonotope_to_Zonotope
import CORALean.ContSet.Zonotope.Real.Operations.RadiusReach

/-!
# `PolyZonotope.radiusReach`

What an interval matrix's radius can add to a coordinate, over every matrix the
interval denotes and every point the polynomial zonotope denotes: the radius
weighted by how far each coordinate can reach, summed over the dependent block
read as independent (`abs_monomial_le_one`) and the independent block itself —
which is exactly `Zonotope.radiusReach` read at the enclosing zonotope, whose
own generators are `G` and `GI` appended.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {m n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What the radius can add to coordinate `i`, over every matrix and every point
denoted, read off the enclosing zonotope. -/
noncomputable def PolyZonotope.radiusReach (IM : Interval (Mat ℝ m n))
    (PZ : PolyZonotope (Vec ℝ n)) (i : Fin m) : ℝ :=
  Zonotope.radiusReach IM PZ.zonotope i

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

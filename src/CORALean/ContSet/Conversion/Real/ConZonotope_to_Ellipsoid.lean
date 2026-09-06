import CORALean.ContSet.Conversion.Real.ConZonotope_to_Zonotope
import CORALean.ContSet.Conversion.Real.Zonotope_to_Ellipsoid

/-!
# A constrained zonotope as an ellipsoid

Through the plain zonotope the constraints are dropped for, then that
zonotope's `√h` ball. A direct enclosure that used the constraints instead of
throwing them away is a separate piece of mathematics.

Loses whatever both steps lose: the constraints, then the cube-to-ball
inflation.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}

noncomputable def ConZonotope.ellipsoid (C : ConZonotope (Vec ℝ n)) : Ellipsoid n :=
  C.zonotope.ellipsoid


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.ellipsoid_outer (C : ConZonotope (Vec ℝ n)) :
    C.construct ⊆ C.ellipsoid.construct :=
  subset_trans C.zonotope_outer (Zonotope.ellipsoid_outer _)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

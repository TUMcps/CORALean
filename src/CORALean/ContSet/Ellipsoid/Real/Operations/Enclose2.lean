import CORALean.ContSet.Ellipsoid.Real.Operations.IsOrOuter

/-!
# `Ellipsoid.enclose₂`

CORA's `@ellipsoid/enclose.m` with two ellipsoids, `enclose(E, E2)`: `E = convHull(E, E2)`, the
hull `orOA` of `Ellipsoid.enclose`.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `enclose(E, E2)`: `E = convHull(E, E2)`. -/
def Ellipsoid.enclose₂ (orOA : Ellipsoid n → Ellipsoid n → Ellipsoid n) (E E2 : Ellipsoid n) :
    Ellipsoid n :=
  orOA E E2


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

import CORALean.ContSet.Ellipsoid.Float.Ellipsoid

/-!
# `Ellipsoid.enclose₂`, over a floating-point scalar

CORA's `enclose(E, E2)`, `convHull(E, E2)`: the hull `orOA` of the two ellipsoids, an argument
owing the contract that its result contains both (CORA's SDP-solver `or(E, E2, 'outer')`).
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Ellipsoid.enclose₂ (orOA : Ellipsoid 𝕋 n → Ellipsoid 𝕋 n → Ellipsoid 𝕋 n)
    (E E2 : Ellipsoid 𝕋 n) : Ellipsoid 𝕋 n :=
  orOA E E2

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

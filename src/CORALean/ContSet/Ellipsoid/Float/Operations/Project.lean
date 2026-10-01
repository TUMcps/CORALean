import CORALean.ContSet.Interval.Float.Operations.Project
import CORALean.ContSet.Ellipsoid.Float.Ellipsoid

/-!
# `Ellipsoid.project` over a floating-point scalar

The centre and the rows of the generator matrix at the chosen coordinates, and the error box
projected with `Interval.project`. Selecting coordinates does no arithmetic, so nothing rounds.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Ellipsoid.project (E : Ellipsoid 𝕋 n) (dims : Fin m → Fin n) : Ellipsoid 𝕋 m where
  k := E.k
  q := fun i => E.q (dims i)
  G := fun i j => E.G (dims i) j
  err := E.err.project dims

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

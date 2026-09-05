import CORALean.ContSet.Ellipsoid.Float.Ellipsoid

/-!
# `Ellipsoid.pullbackAbs`

The magnitude of the direction pulled back into generator space, coordinate
by coordinate. `sqSumUp` of this is what a candidate is checked against.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

/-- The magnitude of the direction pulled back into generator space, coordinate
by coordinate. `sqSumUp` of this is what a candidate is checked against. -/
def Ellipsoid.pullbackAbs (E : Ellipsoid 𝕋 n) (a : Vec 𝕋 n) (j : Fin E.k) : 𝕋 :=
  maximum (dotUp a fun i => E.G i j) (neg (dotDown a fun i => E.G i j))

end CORALean.Float

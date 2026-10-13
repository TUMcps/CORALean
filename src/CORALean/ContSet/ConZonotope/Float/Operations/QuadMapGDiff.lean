import CORALean.ContSet.ConZonotope.Float.Operations.QuadMapGDown
import CORALean.ContSet.ConZonotope.Float.Operations.QuadMapGUp

/-!
# `ConZonotope.quadMapGDiff`

How far a stored generator of `quadMap` can be from the exact one: the gap between its two
roundings, which a coefficient in `[-1,1]` then spreads either way.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The gap between the two roundings of every generator. -/
def ConZonotope.quadMapGDiff (Q : Fin m → Mat 𝕋 n n) (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) :
    Fin m → Fin (cZ.h + cZ.h + cZ.h * cZ.h) → 𝕋 :=
  fun i l => subUp (ConZonotope.quadMapGUp Q cZ i l) (ConZonotope.quadMapGDown Q cZ i l)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

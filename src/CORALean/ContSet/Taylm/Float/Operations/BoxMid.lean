import CORALean.ContSet.Taylm.Float.Taylm

/-!
# `Taylm.boxMid`, over a floating-point scalar

The midpoint of a box, `(l + u) / 2` with the sum rounded up.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.boxMid (B : Fin n → 𝕋 × 𝕋) : Vec 𝕋 n := fun k => half (addUp (B k).1 (B k).2)
end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

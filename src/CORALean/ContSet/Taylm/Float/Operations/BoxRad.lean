import CORALean.ContSet.Taylm.Float.Operations.BoxMid

/-!
# `Taylm.boxRad`, over a floating-point scalar

A radius around the stored midpoint reaching both ends of the box: the larger of the two gaps,
rounded up.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.boxRad (B : Fin n → 𝕋 × 𝕋) : Vec 𝕋 n :=
  fun k => maximum (subUp (B k).2 (Taylm.boxMid B k)) (subUp (Taylm.boxMid B k) (B k).1)
end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

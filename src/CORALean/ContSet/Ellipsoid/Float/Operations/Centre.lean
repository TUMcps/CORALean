import CORALean.ContSet.Ellipsoid.Float.Ellipsoid

/-!
# `Ellipsoid.centre`, over a floating-point scalar

CORA's `@ellipsoid/center` returns the field `q`: the stored centre, in `𝕋`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Ellipsoid.centre (E : Ellipsoid 𝕋 n) : Vec 𝕋 n := E.q

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

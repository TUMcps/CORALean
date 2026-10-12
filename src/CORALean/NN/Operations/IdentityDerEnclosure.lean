import CORALean.ContSet.Interval.Float.Interval
import CORALean.Global.Float.FloatOps

/-!
# The derivative enclosure of the identity
The identity's derivative is `1` everywhere, so the enclosure is the point `[1, 1]`.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

def identityDerEnclosure (_ : Interval 𝕋) : Interval 𝕋 := ⟨one, one⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

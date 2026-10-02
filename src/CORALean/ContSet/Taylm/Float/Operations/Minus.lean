import CORALean.ContSet.Taylm.Float.Operations.Plus
import CORALean.ContSet.Taylm.Float.Operations.Uminus

/-!
# `Taylm.minus`
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.minus (T₁ T₂ : Taylm 𝕋 n) : Taylm 𝕋 n := T₁.plus T₂.uminus

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

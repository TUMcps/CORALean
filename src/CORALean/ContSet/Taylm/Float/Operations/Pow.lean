import CORALean.ContSet.Taylm.Float.Operations.Times
import CORALean.ContSet.Taylm.Float.Operations.Const

/-!
# `Taylm.pow`
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

def Taylm.pow (T : Taylm 𝕋 n) : ℕ → Taylm 𝕋 n
  | 0 => Taylm.const n one T.maxOrder
  | k + 1 => (T.pow k).times T

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

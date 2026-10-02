import CORALean.ContSet.Taylm.Float.Operations.Sum
import CORALean.ContSet.Taylm.Float.Operations.Smul

/-!
# `Taylm.mtimes`

By a float matrix, each entry an exact factor, `smul` at `alo = ahi`.
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

def Taylm.mtimes {k m : ℕ} (M : Mat 𝕋 k m) (T : Fin m → Taylm 𝕋 n) : Fin k → Taylm 𝕋 n :=
  fun i => Taylm.sum fun j => (T j).smul (M i j) (M i j)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

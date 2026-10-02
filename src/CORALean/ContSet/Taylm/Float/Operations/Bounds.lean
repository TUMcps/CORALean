import CORALean.ContSet.Taylm.Float.Operations.PolyBounds

/-!
# The range of a Taylor model
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

def Taylm.bounds (T : Taylm 𝕋 n) : 𝕋 × 𝕋 :=
  (addDown (Taylm.polyBounds T.terms).1 T.remInf, addUp (Taylm.polyBounds T.terms).2 T.remSup)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

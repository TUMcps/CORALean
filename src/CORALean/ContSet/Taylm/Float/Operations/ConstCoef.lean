module

public import CORALean.ContSet.Taylm.Float.Taylm
public import CORALean.ContSet.Taylm.Real.Operations.Degree
public import CORALean.Global.Float.ListSum

@[expose] public section

/-!
# The constant part of a Taylor model

Summed downward; any float is a sound centre, so the rounding costs only precision.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.constCoef (T : Taylm 𝕋 n) : 𝕋 :=
  listSumDown ((T.terms.filter fun a => Real.Taylm.degree a.2 == 0).map Prod.fst)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

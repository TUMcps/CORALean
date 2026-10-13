module

public import CORALean.ContSet.Taylm.Real.Operations.Degree

@[expose] public section

/-!
# The constant part of a Taylor model

CORA's `c_f`, the coefficient at the zero exponent, where the elementary functions expand.
Summed, as the list may repeat the exponent; any centre is sound and this one is CORA's.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.constCoef (T : Taylm n) : ℝ :=
  ((T.terms.filter fun a => Taylm.degree a.2 == 0).map Prod.fst).sum

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

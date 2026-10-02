import CORALean.ContSet.Taylm.Real.Taylm

/-!
# A constant Taylor model

CORA's `aux_addConst` with nothing to add it to: one term at the zero exponent and no
remainder. `compose` subtracts it to centre a model on its constant part.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.const (n : ℕ) (c : ℝ) (N : ℕ) : Taylm n := ⟨[(c, 0)], 0, 0, N⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

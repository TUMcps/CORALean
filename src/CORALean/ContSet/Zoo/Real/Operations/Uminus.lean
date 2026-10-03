import CORALean.ContSet.Zoo.Real.Zoo
import CORALean.ContSet.Taylm.Real.Operations.Uminus
import CORALean.ContSet.Interval.Real.Operations.Uminus

/-!
# `Zoo.uminus`

CORA's unary `-` (`aux_s_uminus`): every member negated.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Zoo.uminus (Z : Zoo n) : Zoo n := ⟨Z.taylm.map Taylm.uminus, Z.ivl.map Interval.uminus⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

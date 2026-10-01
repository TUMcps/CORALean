import CORALean.ContSet.Interval.Real.Interval

/-!
# `Interval.infimum`

CORA's `@interval/infimum`: the lower bound.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Entrywise

variable {α ι : Type} [AddCommGroup α] [Module ℝ α] [Entrywise α ι]


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.infimum (I : Interval α) : α := I.inf

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

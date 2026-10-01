import CORALean.ContSet.Interval.Real.Interval

/-!
# `Interval.supremum`

CORA's `@interval/supremum`: the upper bound.
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

def Interval.supremum (I : Interval α) : α := I.sup

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

import CORALean.ContSet.Interval.Real.Interval

/-!
# `Interval.infimum`

CORA's `@interval/infimum`: the lower bound.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Entrywise

variable {α ι : Type} [AddCommGroup α] [Module ℝ α] [Entrywise α ι]


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.infimum (I : Interval α) : α := I.inf

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

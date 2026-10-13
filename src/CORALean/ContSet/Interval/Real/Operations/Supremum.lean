module

public import CORALean.ContSet.Interval.Real.Interval

@[expose] public section

/-!
# `Interval.supremum`

CORA's `@interval/supremum`: the upper bound.
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

def Interval.supremum (I : Interval α) : α := I.sup

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

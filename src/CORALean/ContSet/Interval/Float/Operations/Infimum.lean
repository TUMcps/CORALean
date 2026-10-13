import CORALean.ContSet.Interval.Float.Interval

/-!
# `Interval.infimum`

The stored lower bound.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.infimum {α : Type} (I : Interval α) : α := I.inf

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

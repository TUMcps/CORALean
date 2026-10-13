import CORALean.ContSet.Interval.Float.Interval

/-!
# `Interval.supremum`

The stored upper bound.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.supremum {α : Type} (I : Interval α) : α := I.sup

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

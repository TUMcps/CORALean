import CORALean.ContSet.Interval.Float.Interval

/-!
# `Interval.supremum`

The stored upper bound.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.supremum {α : Type} (I : Interval α) : α := I.sup

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

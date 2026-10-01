import CORALean.ContSet.Interval.Float.Interval

/-!
# `Interval.uplus`

Unary plus, the identity, over any stored ambient type.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.uplus {α : Type} (I : Interval α) : Interval α := I

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

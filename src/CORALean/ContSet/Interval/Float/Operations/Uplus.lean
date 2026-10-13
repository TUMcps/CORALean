module

public import CORALean.ContSet.Interval.Float.Interval

@[expose] public section

/-!
# `Interval.uplus`

Unary plus, the identity, over any stored ambient type.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.uplus {α : Type} (I : Interval α) : Interval α := I

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

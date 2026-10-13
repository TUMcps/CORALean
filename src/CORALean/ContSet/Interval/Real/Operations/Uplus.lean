import CORALean.ContSet.Interval.Real.Interval

/-!
# `Interval.uplus`

CORA's `@interval/uplus`: unary plus, the identity.
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

def Interval.uplus (I : Interval α) : Interval α := I

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

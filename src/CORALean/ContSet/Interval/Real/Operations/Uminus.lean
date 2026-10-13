import CORALean.ContSet.Interval.Real.Interval

/-!
# `Interval.uminus`

CORA's `@interval/uminus`: negation swaps the bounds, `[a, b]` becoming `[-b, -a]`.
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

def Interval.uminus (I : Interval α) : Interval α where
  inf := -I.sup
  sup := -I.inf

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

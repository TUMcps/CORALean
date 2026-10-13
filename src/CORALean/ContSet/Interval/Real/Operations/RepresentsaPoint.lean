import CORALean.ContSet.Interval.Real.Interval

/-!
# `Interval.representsa_point`

CORA's `@interval/representsa_` at type `point` with tolerance `0`: every radius is zero, that is
`inf = sup`. A crossed box has negative radius, so it is not a point.
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

def Interval.representsa_point (I : Interval α) : Prop := I.inf = I.sup


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

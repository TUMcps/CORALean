import CORALean.ContSet.Interval.Real.Operations.Or

/-!
# `Interval.convHull`

CORA's `@interval/convHull_` at two intervals: it ends in `I | S`, so it is `or`. The hull of
two boxes is not their union, and the box hull is the smallest box containing it.
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

def Interval.convHull (I₁ I₂ : Interval α) : Interval α := I₁.or I₂

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

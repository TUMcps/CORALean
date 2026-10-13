import CORALean.ContSet.EmptySet.Real.EmptySet
import CORALean.ContSet.Interval.Real.Operations.Empty

/-!
# `EmptySet.interval`

CORA's `@emptySet/interval`: `interval.empty(n)`, the crossed box `Interval.empty`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `emptySet/interval`: `Interval.empty n`. -/
def EmptySet.interval (_ : EmptySet n) : Interval (Vec ℝ n) := Interval.empty n

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

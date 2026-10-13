module

public import CORALean.ContSet.Interval.Real.Operations.Point

@[expose] public section

/-!
# `Interval.origin`

CORA's `@interval/origin`: the point interval at the origin of `ℝⁿ`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Entrywise


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.origin (n : ℕ) : Interval (Vec ℝ n) := Interval.point 0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.ContSet.Fullspace.Real.Fullspace

@[expose] public section

/-!
# `Fullspace.centre`

CORA's `center` of the full space: the origin, `zeros(n, 1)`. At `n = 0` CORA returns
`NaN` for want of a vector to return; `Vec ℝ 0` has the one element `0`, which is it.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The origin. -/
def Fullspace.centre (_ : Fullspace n) : Vec ℝ n := 0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

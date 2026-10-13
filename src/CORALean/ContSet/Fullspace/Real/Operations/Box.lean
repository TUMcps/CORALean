module

public import CORALean.ContSet.Fullspace.Real.Fullspace

@[expose] public section

/-!
# `Fullspace.box`

CORA's `@fullspace/box`: the full space itself, which is its own smallest enclosing box
(an interval with infinite endpoints, which `Interval` cannot hold).
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `fullspace/box`: the full space. -/
def Fullspace.box (F : Fullspace n) : Fullspace n := F

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

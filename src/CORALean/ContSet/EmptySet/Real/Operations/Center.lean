module

public import CORALean.ContSet.EmptySet.Real.EmptySet

@[expose] public section

/-!
# `EmptySet.center`

CORA's `@emptySet/center`: `double.empty(n, 0)`, an `n × 0` matrix, the answer "there is no
center". `none`, which a `Vec ℝ n` cannot say.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `emptySet/center`: no point. -/
def EmptySet.center (_ : EmptySet n) : Option (Vec ℝ n) := none

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

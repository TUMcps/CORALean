import CORALean.ContSet.EmptySet.Real.EmptySet

/-!
# `EmptySet.empty`

CORA's `emptySet.empty(n)`: the empty set in `n` dimensions, the only value of the type.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `emptySet.empty(n)`. -/
def EmptySet.empty (n : ℕ) : EmptySet n := ⟨⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

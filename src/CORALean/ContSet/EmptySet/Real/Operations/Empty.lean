import CORALean.ContSet.EmptySet.Real.EmptySet

/-!
# `EmptySet.empty`

CORA's `emptySet.empty(n)`: the empty set in `n` dimensions, the only value of the type.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `emptySet.empty(n)`. -/
def EmptySet.empty (n : ℕ) : EmptySet n := ⟨⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

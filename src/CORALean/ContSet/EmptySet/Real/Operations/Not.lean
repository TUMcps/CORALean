import CORALean.ContSet.EmptySet.Real.EmptySet
import CORALean.ContSet.Fullspace.Real.Fullspace

/-!
# `EmptySet.not`

CORA's `@emptySet/not`: the complement of the empty set is the full space of the same
dimension.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `emptySet/not`. -/
def EmptySet.not (_ : EmptySet n) : Fullspace n := ⟨⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

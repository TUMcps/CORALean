import CORALean.ContSet.EmptySet.Real.EmptySet
import CORALean.ContSet.ContSet.ContSet

/-!
# `EmptySet.convHull`

CORA's `@emptySet/convHull_`: the hull of the empty set and `S` is `S`, returned as it is.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `emptySet/convHull_`: the other operand. -/
def EmptySet.convHull (_ : EmptySet n) {S : Type} (s : S) : S := s

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

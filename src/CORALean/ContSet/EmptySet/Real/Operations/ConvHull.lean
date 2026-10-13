import CORALean.ContSet.EmptySet.Real.EmptySet
import CORALean.ContSet.ContSet.ContSet

/-!
# `EmptySet.convHull`

CORA's `@emptySet/convHull_`: the hull of the empty set and `S` is `S`, returned as it is.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `emptySet/convHull_`: the other operand. -/
def EmptySet.convHull (_ : EmptySet n) {S : Type} (s : S) : S := s

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

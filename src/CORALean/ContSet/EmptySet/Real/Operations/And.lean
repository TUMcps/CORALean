import CORALean.ContSet.EmptySet.Real.EmptySet

/-!
# `EmptySet.and_`

CORA's `@emptySet/and_`: the intersection with anything is the empty set again, returned
as it stands. Generic over the other operand, whatever representation it is in.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `emptySet/and_`: the operand `E` itself, whatever it is intersected with. -/
def EmptySet.and_ {S : Type} (E : EmptySet n) (_ : S) : EmptySet n := E

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

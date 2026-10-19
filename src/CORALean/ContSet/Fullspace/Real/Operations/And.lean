module

public import CORALean.ContSet.Fullspace.Real.Fullspace

@[expose] public section

/-!
# `Fullspace.and_`

CORA's `@fullspace/and_`: the intersection with anything is that operand, returned as it
stands. Generic over the other operand, whatever representation it is in.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      19-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `fullspace/and_`: the other operand. -/
def Fullspace.and_ {S : Type} (_ : Fullspace n) (s : S) : S := s

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

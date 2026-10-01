import CORALean.ContSet.Fullspace.Real.Fullspace
import CORALean.ContSet.EmptySet.Real.EmptySet

/-!
# `Fullspace.not`

CORA's `@fullspace/not`: the complement of the full space is the empty set of the same
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

/-- `fullspace/not`. -/
def Fullspace.not (_ : Fullspace n) : EmptySet n := ⟨⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

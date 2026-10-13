module

public import CORALean.ContSet.Fullspace.Real.Fullspace
public import CORALean.ContSet.EmptySet.Real.EmptySet

@[expose] public section

/-!
# `Fullspace.not`

CORA's `@fullspace/not`: the complement of the full space is the empty set of the same
dimension.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `fullspace/not`. -/
def Fullspace.not (_ : Fullspace n) : EmptySet n := ⟨⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

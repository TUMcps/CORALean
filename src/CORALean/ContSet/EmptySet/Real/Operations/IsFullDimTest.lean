import CORALean.ContSet.EmptySet.Real.EmptySet

/-!
# `EmptySet.isFullDimTest`

CORA's `isFullDim` of the emptyset, as the `Bool` it answers: always `false`: the interior of `∅`
is empty. Holds no scalar and computes nothing numeric; `EmptySet.isFullDimTest_iff` says it is
the interior being nonempty.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def EmptySet.isFullDimTest (_ : EmptySet n) : Bool := false

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

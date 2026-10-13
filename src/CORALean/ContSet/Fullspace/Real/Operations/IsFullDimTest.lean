import CORALean.ContSet.Fullspace.Real.Fullspace

/-!
# `Fullspace.isFullDimTest`

CORA's `isFullDim` of the fullspace, as the `Bool` it answers: always `true`: the interior of the
whole space is itself. Holds no scalar and computes nothing numeric; `Fullspace.isFullDimTest_iff`
says it is the interior being nonempty.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Fullspace.isFullDimTest (_ : Fullspace n) : Bool := true

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

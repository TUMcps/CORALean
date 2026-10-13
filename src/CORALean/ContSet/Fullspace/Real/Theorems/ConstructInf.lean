module

public import CORALean.ContSet.Fullspace.Real.Operations.Inf

@[expose] public section

/-!
# `Fullspace.Inf` denotes everything
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Fullspace.construct_Inf : (Fullspace.Inf n).construct = (Set.univ : Set (Vec ℝ n)) := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

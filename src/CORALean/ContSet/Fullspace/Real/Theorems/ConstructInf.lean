import CORALean.ContSet.Fullspace.Real.Operations.Inf

/-!
# `Fullspace.Inf` denotes everything
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Fullspace.construct_Inf : (Fullspace.Inf n).construct = (Set.univ : Set (Vec ℝ n)) := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

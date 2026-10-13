import CORALean.ContSet.EmptySet.Real.Operations.Empty
import CORALean.ContSet.EmptySet.Real.Instances

/-!
# `EmptySet.empty` denotes `∅`
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open ContSet

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem EmptySet.construct_empty : construct (EmptySet.empty n) = (∅ : Set (Vec ℝ n)) := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

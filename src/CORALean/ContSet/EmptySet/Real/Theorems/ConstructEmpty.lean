import CORALean.ContSet.EmptySet.Real.Operations.Empty
import CORALean.ContSet.EmptySet.Real.Instances

/-!
# `EmptySet.empty` denotes `∅`
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open ContSet

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem EmptySet.construct_empty : construct (EmptySet.empty n) = (∅ : Set (Vec ℝ n)) := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

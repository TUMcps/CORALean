import CORALean.ContSet.EmptySet.Real.Operations.Not
import CORALean.ContSet.EmptySet.Real.Instances
import CORALean.ContSet.Fullspace.Real.Instances

/-!
# `EmptySet.not` is the complement
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

theorem EmptySet.not_exact (E : EmptySet n) : E.not.construct = (E.construct)ᶜ := by
  change (Set.univ : Set (Vec ℝ n)) = (∅ : Set (Vec ℝ n))ᶜ
  exact Set.compl_empty.symm

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

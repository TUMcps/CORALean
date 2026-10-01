import CORALean.ContSet.Capsule.Real.Operations.Empty
import CORALean.ContSet.Capsule.Real.Theorems.ConstructEqEmpty

/-!
# `Capsule.empty` denotes the empty set


-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Capsule.empty_exact (n : ℕ) : (Capsule.empty n).construct = ∅ :=
  Capsule.construct_eq_empty (by simp [Capsule.empty])

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

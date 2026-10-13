module

public import CORALean.ContSet.Capsule.Real.Operations.Empty
public import CORALean.ContSet.Capsule.Real.Theorems.ConstructEqEmpty

@[expose] public section

/-!
# `Capsule.empty` denotes the empty set


-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Capsule.empty_exact (n : ℕ) : (Capsule.empty n).construct = ∅ :=
  Capsule.construct_eq_empty (by simp [Capsule.empty])

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

import CORALean.ContSet.EmptySet.Real.EmptySet
import CORALean.ContSet.EmptySet.Real.Instances

/-!
# The empty set is not a point

`representsa_(O,'point')` and `'origin'` are `false` for `emptySet`.
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

theorem EmptySet.construct_ne_singleton (E : EmptySet n) (v : Vec ℝ n) :
    construct E ≠ {v} := by
  intro h
  have : v ∈ construct E := by rw [h]; exact Set.mem_singleton v
  exact this.elim

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

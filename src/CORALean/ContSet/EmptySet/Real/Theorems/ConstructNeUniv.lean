import CORALean.ContSet.EmptySet.Real.EmptySet
import CORALean.ContSet.EmptySet.Real.Instances

/-!
# The empty set is not the full space

`representsa_(O,'fullspace')` is `false` for `emptySet`: `Vec ℝ n` has a point
at every `n`, the zero vector at `n = 0` included.
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

theorem EmptySet.construct_ne_univ (E : EmptySet n) : construct E ≠ Set.univ := by
  intro h
  have : (0 : Vec ℝ n) ∈ construct E := by rw [h]; exact Set.mem_univ _
  exact this.elim

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

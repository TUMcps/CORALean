module

public import CORALean.ContSet.EmptySet.Real.EmptySet
public import CORALean.ContSet.EmptySet.Real.Instances

@[expose] public section

/-!
# The empty set is not the full space

`representsa_(O,'fullspace')` is `false` for `emptySet`: `Vec ℝ n` has a point
at every `n`, the zero vector at `n = 0` included.

## Inputs
* `E` – empty set

## Hypotheses
* none

## Conclusion
* the empty set is not the full space
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

theorem EmptySet.construct_ne_univ (E : EmptySet n) : construct E ≠ Set.univ := by
  intro h
  have : (0 : Vec ℝ n) ∈ construct E := by rw [h]; exact Set.mem_univ _
  exact this.elim

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

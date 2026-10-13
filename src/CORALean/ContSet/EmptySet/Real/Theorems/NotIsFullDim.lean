import CORALean.ContSet.ContSet.Definitions.IsFullDim
import CORALean.ContSet.EmptySet.Real.Instances

/-!
# The empty set is not full-dimensional

Its interior is `∅`, in every dimension.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open ContSet

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem EmptySet.not_isFullDim (E : EmptySet n) : ¬ ContSet.IsFullDim E := by
  change ¬ (interior (∅ : Set (Vec ℝ n))).Nonempty
  rw [interior_empty]
  exact Set.not_nonempty_empty

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

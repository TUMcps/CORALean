import CORALean.ContSet.EmptySet.Real.Operations.IsFullDimTest
import CORALean.ContSet.EmptySet.Real.Instances

/-!
# `EmptySet.isFullDimTest` is full-dimensionality

The `Bool` `EmptySet.isFullDimTest` is `true` exactly when the interior of the set is nonempty:
exact.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem EmptySet.isFullDimTest_iff (F : EmptySet n) :
    F.isFullDimTest = true ↔ (interior F.construct).Nonempty := by
  rw [EmptySet.isFullDimTest]
  simp [EmptySet.construct]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

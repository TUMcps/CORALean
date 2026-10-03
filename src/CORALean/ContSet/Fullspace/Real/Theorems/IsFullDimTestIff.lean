import CORALean.ContSet.Fullspace.Real.Operations.IsFullDimTest
import CORALean.ContSet.Fullspace.Real.Theorems.IsFullDim

/-!
# `Fullspace.isFullDimTest` is full-dimensionality

The `Bool` `Fullspace.isFullDimTest` is `true` exactly when the interior of the set is nonempty:
exact.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Fullspace.isFullDimTest_iff (F : Fullspace n) :
    F.isFullDimTest = true ↔ (interior F.construct).Nonempty := by
  rw [Fullspace.isFullDimTest]
  simp [Fullspace.isFullDim F]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

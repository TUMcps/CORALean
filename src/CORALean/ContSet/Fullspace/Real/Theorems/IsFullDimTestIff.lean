module

public import CORALean.ContSet.Fullspace.Real.Operations.IsFullDimTest
public import CORALean.ContSet.Fullspace.Real.Theorems.IsFullDim

@[expose] public section

/-!
# `Fullspace.isFullDimTest` is full-dimensionality

The `Bool` `Fullspace.isFullDimTest` is `true` exactly when the interior of the set is nonempty:
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

theorem Fullspace.isFullDimTest_iff (F : Fullspace n) :
    F.isFullDimTest = true ↔ (interior F.construct).Nonempty := by
  rw [Fullspace.isFullDimTest]
  simp [Fullspace.isFullDim F]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

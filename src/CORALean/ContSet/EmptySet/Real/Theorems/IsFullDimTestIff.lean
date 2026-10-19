module

public import CORALean.ContSet.EmptySet.Real.Operations.IsFullDimTest
public import CORALean.ContSet.EmptySet.Real.Instances

@[expose] public section

/-!
# `EmptySet.isFullDimTest` is full-dimensionality

The `Bool` `EmptySet.isFullDimTest` is `true` exactly when the interior of the set is nonempty:
exact.

## Inputs
* `F` – empty set

## Hypotheses
* none

## Conclusion
* the test answers true iff the interior is nonempty
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

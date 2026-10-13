import CORALean.ContSet.ContSet.Theorems.SubsetMinkowskiDiffIff

/-!
# Adding `T` back to a Minkowski difference stays inside `S`

The defining property, read off the Galois connection at `X := minkowskiDiff S T`
— an *inner* statement, and the one an algorithm uses: whatever a `MinkDiff`
implementation returns still absorbs all of `T` without leaving `S`.
-/

-- Authors:       Claude Opus 5
-- Written:       08-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Pointwise

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The counit of the adjunction: `minkowskiDiff S T` is exactly what `T` may be
added to. -/
theorem minkowskiDiff_add_subset (S T : Set α) : minkowskiDiff S T + T ⊆ S :=
  (subset_minkowskiDiff_iff _ S T).mp subset_rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

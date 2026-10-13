import CORALean.ContSet.ContSet.Definitions.CompactSet

/-!
# A compact representation's set is bounded

`CompactSet.isBounded_construct`: compactness over a normed space gives boundedness for free.
-/

-- Authors:       Claude Sonnet 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {S α : Type} [NormedAddCommGroup α] [NormedSpace ℝ α] [ContSet S α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem CompactSet.isBounded_construct [CompactSet S α] (s : S) :
    Bornology.IsBounded (construct s) :=
  (CompactSet.isCompact_construct s).isBounded

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

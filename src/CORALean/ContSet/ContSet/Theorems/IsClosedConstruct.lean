module

public import CORALean.ContSet.ContSet.Definitions.CompactSet

@[expose] public section

/-!
# A compact representation's set is closed

`CompactSet.isClosed_construct`: compactness over a normed space gives closedness for free.
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

theorem CompactSet.isClosed_construct [CompactSet S α] (s : S) : IsClosed (construct s) :=
  (CompactSet.isCompact_construct s).isClosed

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

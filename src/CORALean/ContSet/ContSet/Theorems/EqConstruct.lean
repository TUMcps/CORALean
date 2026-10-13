module

public import CORALean.ContSet.ContSet.Operations.Eq

@[expose] public section

/-!
# `eq` is sound: equal means the same set
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {S α : Type} [ContSet S α] [Isequal S]


-- =======================================  MAIN THEOREM  ======================================= --

/-- If `eq` holds the two representations denote one set. Sound, not exact: `eq` can fail on
two representations of one set. -/
theorem ContSet.eq_construct {s t : S} (h : ContSet.eq s t) : construct s = construct t :=
  Isequal.isequal_construct s t h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

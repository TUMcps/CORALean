module

public import CORALean.ContSet.ContSet.Operations.Ne

@[expose] public section

/-!
# `ne` holds on sets that differ
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

/-- If the denoted sets differ, `ne` holds. Only this direction: `ne` can hold of two
representations of one set, since `isequal` is conservative. -/
theorem ContSet.ne_of_construct_ne {s t : S} (h : construct s ≠ construct t) : ContSet.ne s t :=
  fun hi => h (Isequal.isequal_construct s t hi)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

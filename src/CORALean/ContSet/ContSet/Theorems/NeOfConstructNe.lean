import CORALean.ContSet.ContSet.Operations.Ne

/-!
# `ne` holds on sets that differ
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


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

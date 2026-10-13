module

public import CORALean.ContSet.ContSet.Operations.Uplus

@[expose] public section

/-!
# `uplus` is exact
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Scalar

variable {S α : Type} [ContSet S α]


-- =======================================  MAIN THEOREM  ======================================= --

/-- `uplus` denotes the set it is given, so it is exact, not only an outer bound. -/
theorem ContSet.uplus_exact (s : S) : construct (ContSet.uplus s) = construct s := rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

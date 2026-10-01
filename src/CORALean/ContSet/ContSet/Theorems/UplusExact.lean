import CORALean.ContSet.ContSet.Operations.Uplus

/-!
# `uplus` is exact
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Scalar

variable {S α : Type} [ContSet S α]


-- =======================================  MAIN THEOREM  ======================================= --

/-- `uplus` denotes the set it is given, so it is exact, not only an outer bound. -/
theorem ContSet.uplus_exact (s : S) : construct (ContSet.uplus s) = construct s := rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

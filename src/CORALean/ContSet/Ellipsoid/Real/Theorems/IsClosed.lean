import CORALean.ContSet.Ellipsoid.Real.Theorems.IsCompact

/-!
# An ellipsoid is closed

Read off compactness, as for a zonotope and for the same reason: `construct` is
an affine image, and an affine image of a merely closed set need not be closed.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   04-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.isClosed_construct (E : Ellipsoid n) : IsClosed E.construct :=
  E.isCompact_construct.isClosed

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

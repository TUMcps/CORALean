import CORALean.ContSet.Ellipsoid.Real.Theorems.IsCompact

/-!
# An ellipsoid is bounded

Read off compactness rather than proved again: `‖G u‖ ≤ ‖G‖ ‖u‖₂` would need the
operator norm, and the compactness proof already carries everything.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

variable {n : ℕ}

theorem Ellipsoid.isBounded_construct (E : Ellipsoid n) : Bornology.IsBounded E.construct :=
  E.isCompact_construct.isBounded

end CORALean.Real

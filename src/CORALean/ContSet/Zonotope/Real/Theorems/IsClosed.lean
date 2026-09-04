import CORALean.ContSet.Zonotope.Real.Theorems.IsCompact

/-!
# A zonotope is closed

Read off compactness rather than proved directly, because an affine image of a
merely closed set need not be closed. Closedness on its own is what the
integrand of a set-valued integral is asked for.
-/

-- Authors:       Tobias Ladner
-- Written:       19-August-2026
-- Last update:   04-September-2026
-- Last revision: ---

namespace CORALean.Real

variable {α : Type} [NormedAddCommGroup α] [NormedSpace ℝ α]

theorem Zonotope.isClosed_construct (Z : Zonotope α) : IsClosed Z.construct :=
  Z.isCompact_construct.isClosed

end CORALean.Real

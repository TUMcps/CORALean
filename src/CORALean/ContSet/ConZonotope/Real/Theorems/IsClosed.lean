import CORALean.ContSet.ConZonotope.Real.Theorems.IsCompact

/-!
# A constrained zonotope is closed

Read off compactness. The halfspace description behind `domain` is closed on its
own, but `construct` is an image of it, and an image of a merely closed set need
not be closed.
-/

-- Authors:       Tobias Ladner
-- Written:       01-September-2026
-- Last update:   04-September-2026
-- Last revision: ---

namespace CORALean.Real

variable {α : Type} [NormedAddCommGroup α] [NormedSpace ℝ α]

theorem ConZonotope.isClosed_construct (C : ConZonotope α) : IsClosed C.construct :=
  C.isCompact_construct.isClosed

end CORALean.Real

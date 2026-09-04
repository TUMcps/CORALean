import CORALean.ContSet.VPolytope.Real.Theorems.IsCompact

/-!
# A vertex description is closed

Read off compactness. A halfspace description proves its own closedness
directly, having no compactness to read it off.
-/

-- Authors:       Tobias Ladner
-- Written:       01-September-2026
-- Last update:   04-September-2026
-- Last revision: ---

namespace CORALean.Real

variable {α : Type} [NormedAddCommGroup α] [NormedSpace ℝ α]

theorem VPolytope.isClosed_construct (P : VPolytope α) : IsClosed P.construct :=
  P.isCompact_construct.isClosed

end CORALean.Real

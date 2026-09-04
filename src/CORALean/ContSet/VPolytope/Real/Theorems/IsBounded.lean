import CORALean.ContSet.VPolytope.Real.Theorems.IsCompact

/-!
# A vertex description is bounded

Read off compactness. This is what a halfspace description cannot have: it
admits unbounded sets, which is the difference between the two representations.
-/

-- Authors:       Tobias Ladner
-- Written:       01-September-2026
-- Last update:   04-September-2026
-- Last revision: ---

namespace CORALean.Real

variable {α : Type} [NormedAddCommGroup α] [NormedSpace ℝ α]

theorem VPolytope.isBounded_construct (P : VPolytope α) : Bornology.IsBounded P.construct :=
  P.isCompact_construct.isBounded

end CORALean.Real

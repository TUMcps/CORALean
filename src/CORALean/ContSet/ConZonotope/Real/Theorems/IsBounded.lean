import CORALean.ContSet.ConZonotope.Real.Theorems.IsCompact

/-!
# A constrained zonotope is bounded

Read off compactness rather than from the generator norms, as the zonotope's is:
the constraints only shrink the coefficient set, so the bound would be the same
one, and there is nothing to gain from proving it twice.
-/

-- Authors:       Tobias Ladner
-- Written:       01-September-2026
-- Last update:   04-September-2026
-- Last revision: ---

namespace CORALean.Real

variable {α : Type} [NormedAddCommGroup α] [NormedSpace ℝ α]

theorem ConZonotope.isBounded_construct (C : ConZonotope α) :
    Bornology.IsBounded C.construct :=
  C.isCompact_construct.isBounded

end CORALean.Real

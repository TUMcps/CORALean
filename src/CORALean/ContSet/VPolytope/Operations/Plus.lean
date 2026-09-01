import CORALean.ContSet.VPolytope.VPolytope

/-!
# `VPolytope.plus`

CORA's `@polytope/plus` on a vertex description: every vertex of one added to
every vertex of the other, so the count multiplies. Exact, and the operation
vertices are for — a halfspace description has no counterpart.

`finProdFinEquiv` is what keeps the index a single `Fin`, matching the field.
-/

-- Authors:       Tobias Ladner
-- Written:       01-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]

def VPolytope.plus (P₁ P₂ : VPolytope α) : VPolytope α where
  k := P₁.k * P₂.k
  V := fun l => P₁.V (finProdFinEquiv.symm l).1 + P₂.V (finProdFinEquiv.symm l).2

end CORALean.Real

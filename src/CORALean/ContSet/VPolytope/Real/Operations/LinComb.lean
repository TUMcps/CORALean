import CORALean.ContSet.VPolytope.Real.VPolytope

/-!
# `VPolytope.linComb`

The vertex lists concatenate, giving the convex hull of the union — which for
two convex sets is exactly CORA's `linComb`, every point of a segment between
them included.
-/

-- Authors:       Tobias Ladner
-- Written:       01-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]

def VPolytope.linComb (P₁ P₂ : VPolytope α) : VPolytope α where
  k := P₁.k + P₂.k
  V := Fin.append P₁.V P₂.V

end CORALean.Real

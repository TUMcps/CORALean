import CORALean.ContSet.Interval.Float.Operations.LinComb
import CORALean.ContSet.VPolytope.Float.VPolytope

/-!
# `VPolytope.linComb`

The vertex lists concatenate, which copies floats and computes none, so nothing
rounds and the box only has to hold what the two incoming boxes did. The one
operation a vertex description performs exactly in floating point.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

def VPolytope.linComb (P₁ P₂ : VPolytope 𝕋 n) : VPolytope 𝕋 n where
  k := P₁.k + P₂.k
  V := fun i => Fin.append (P₁.V i) (P₂.V i)
  E := P₁.E.linComb P₂.E

end CORALean.Float

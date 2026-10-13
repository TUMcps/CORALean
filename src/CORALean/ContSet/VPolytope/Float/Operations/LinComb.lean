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


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def VPolytope.linComb (P₁ P₂ : VPolytope (Vec 𝕋 n)) : VPolytope (Vec 𝕋 n) where
  k := P₁.k + P₂.k
  V := Fin.append P₁.V P₂.V
  E := P₁.E.linComb P₂.E

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

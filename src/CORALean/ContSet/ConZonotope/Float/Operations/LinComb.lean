import CORALean.ContSet.ConZonotope.Float.Operations.Zonotope
import CORALean.ContSet.Zonotope.Float.Operations.LinComb

/-!
# `ConZonotope.linComb`

Taken on the enclosing zonotopes, as over ℝ, so the result carries no
constraints and the rounding is the zonotope's.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

def ConZonotope.linComb (C₁ C₂ : ConZonotope 𝕋 n) : ConZonotope 𝕋 n :=
  (C₁.zonotope.linComb C₂.zonotope).conZonotope

end CORALean.Float

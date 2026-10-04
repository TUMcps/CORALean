import CORALean.ContSet.Zonotope.Float.Operations.StGamma
import CORALean.ContSet.Zonotope.Float.Operations.StBeta

/-!
# `Zonotope.stUsed`

What the two kinds of coefficient use of the unit budget, rounded up.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Zonotope.stUsed (Z₂ Z₁ : Zonotope 𝕋 n) (H : Mat 𝕋 Z₂.h n) (k : Fin Z₂.h) : 𝕋 :=
  addUp (absolute (Z₂.stBeta Z₁ H k)) (sumUp fun j => absolute (Z₂.stGamma Z₁ H k j))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

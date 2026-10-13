import CORALean.ContSet.Zonotope.Float.Operations.StUsed

/-!
# `Zonotope.stDelta`

Half of the budget's slack, rounded down: the size of correction the box may use.
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

def Zonotope.stDelta (Z₂ Z₁ : Zonotope (Vec 𝕋 n)) (H : Mat 𝕋 Z₂.h n) : 𝕋 :=
  half (subDown one (maximumOver (Z₂.stUsed Z₁ H)))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

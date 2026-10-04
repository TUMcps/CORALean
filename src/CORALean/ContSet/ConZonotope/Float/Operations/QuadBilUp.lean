import CORALean.ContSet.PolyZonotope.Float.Operations.QuadUp
import CORALean.ContSet.ConZonotope.Float.ConZonotope

/-!
# `ConZonotope.quadBilUp`

The bilinear form `u ⬝ᵥ (Q *ᵥ v)` rounded up, the mirror of `quadBilDown`.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `u ⬝ᵥ (Q *ᵥ v)`, from above. -/
def ConZonotope.quadBilUp (Q : Mat 𝕋 n n) (u v : Vec 𝕋 n) : 𝕋 :=
  PolyZonotope.quadUp u (mulVecDown Q v) (mulVecUp Q v)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

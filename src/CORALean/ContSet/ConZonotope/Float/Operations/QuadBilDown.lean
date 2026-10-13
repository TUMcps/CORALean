import CORALean.ContSet.PolyZonotope.Float.Operations.QuadDown
import CORALean.ContSet.ConZonotope.Float.ConZonotope

/-!
# `ConZonotope.quadBilDown`

The bilinear form `u ⬝ᵥ (Q *ᵥ v)` rounded down: `Q *ᵥ v` in both directions first, then the
products against `u` over that interval, as `PolyZonotope.quadMap` does for its generators.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `u ⬝ᵥ (Q *ᵥ v)`, from below. -/
def ConZonotope.quadBilDown (Q : Mat 𝕋 n n) (u v : Vec 𝕋 n) : 𝕋 :=
  PolyZonotope.quadDown u (mulVecDown Q v) (mulVecUp Q v)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

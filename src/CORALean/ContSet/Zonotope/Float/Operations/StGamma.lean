import CORALean.ContSet.Zonotope.Float.Zonotope

/-!
# `Zonotope.stGamma`

The approximate coefficients of the generators, `H G₁`.
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

def Zonotope.stGamma (Z₂ Z₁ : Zonotope 𝕋 n) (H : Mat 𝕋 Z₂.h n) : Mat 𝕋 Z₂.h Z₁.h :=
  fun k j => dotDown (H k) fun l => Z₁.G l j

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

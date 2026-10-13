import CORALean.ContSet.ConZonotope.Float.ConZonotope

/-!
# `ConZonotope.centreLo`

A lower end of `y₀ = c + G β₀`, each entry rounded downward.
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

def ConZonotope.centreLo (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) (β₀ : Vec 𝕋 cZ.h) : Vec 𝕋 n := fun i =>
  addDown (cZ.c i) (dotDown (fun j => cZ.G j i) β₀)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

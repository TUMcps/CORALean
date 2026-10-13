import CORALean.ContSet.ConZonotope.Float.ConZonotope

/-!
# `ConZonotope.centreHi`

An upper end of `y₀ = c + G β₀`, each entry rounded upward.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ConZonotope.centreHi (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) (β₀ : Vec 𝕋 cZ.h) : Vec 𝕋 n := fun i =>
  addUp (cZ.c i) (dotUp (fun j => cZ.G j i) β₀)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

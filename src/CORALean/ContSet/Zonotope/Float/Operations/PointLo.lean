import CORALean.ContSet.Zonotope.Float.Zonotope

/-!
# `Zonotope.pointLo`

A lower end of `c + G β` for a coefficient vector `β`, each entry rounded downward.
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

def Zonotope.pointLo (Z : Zonotope (Vec 𝕋 n)) (β : Vec 𝕋 Z.h) : Vec 𝕋 n := fun i =>
  addDown (Z.c i) (dotDown (fun j => Z.G j i) β)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

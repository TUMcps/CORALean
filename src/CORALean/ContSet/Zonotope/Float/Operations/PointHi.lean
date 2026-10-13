import CORALean.ContSet.Zonotope.Float.Zonotope

/-!
# `Zonotope.pointHi`

An upper end of `c + G β` for a coefficient vector `β`, each entry rounded upward.
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

def Zonotope.pointHi (Z : Zonotope (Vec 𝕋 n)) (β : Vec 𝕋 Z.h) : Vec 𝕋 n := fun i =>
  addUp (Z.c i) (dotUp (fun j => Z.G j i) β)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

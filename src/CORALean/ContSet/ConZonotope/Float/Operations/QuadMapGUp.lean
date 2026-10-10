import CORALean.ContSet.ConZonotope.Float.Operations.QuadBilDown
import CORALean.ContSet.ConZonotope.Float.Operations.QuadBilUp

/-!
# `ConZonotope.quadMapGUp`

The generators of `quadMapGDown` rounded up. Their gap to the lower ones is what the stored
generators can be wrong by.
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

/-- The generators of the enclosing zonotope, each rounded up. -/
def ConZonotope.quadMapGUp (Q : Fin m → Mat 𝕋 n n) (cZ : ConZonotope 𝕋 n) :
    Fin m → Fin (cZ.h + cZ.h + cZ.h * cZ.h) → 𝕋 :=
  fun i => Fin.append
    (Fin.append
      (fun j => addUp (ConZonotope.quadBilUp (Q i) cZ.c (cZ.G j))
        (ConZonotope.quadBilUp (Q i) (cZ.G j) cZ.c))
      (fun j => half (ConZonotope.quadBilUp (Q i) (cZ.G j) (cZ.G j))))
    (fun l =>
      if (finProdFinEquiv.symm l).1 < (finProdFinEquiv.symm l).2
      then addUp
        (ConZonotope.quadBilUp (Q i) (cZ.G (finProdFinEquiv.symm l).1)
          (cZ.G (finProdFinEquiv.symm l).2))
        (ConZonotope.quadBilUp (Q i) (cZ.G (finProdFinEquiv.symm l).2)
          (cZ.G (finProdFinEquiv.symm l).1))
      else zero)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

import CORALean.ContSet.PolyZonotope.Float.Operations.ExtG
import CORALean.ContSet.PolyZonotope.Float.Operations.QuadUp

/-!
# `quadMap`'s generators, rounded up

Split out of `QuadMap.lean` (issue #62): read again by `quadMapGDiff` in this
directory and by `Theorems/QuadMapOuter.lean`, both outside this file.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def PolyZonotope.quadMapGUp (Q : Fin m → Mat 𝕋 n n) (S : PolyZonotope 𝕋 n) :
    Mat 𝕋 m ((S.h + 1) * (S.h + 1)) :=
  fun k l => PolyZonotope.quadUp (fun r => PolyZonotope.extG S r (finProdFinEquiv.symm l).1)
    (mulVecDown (Q k) fun r => PolyZonotope.extG S r (finProdFinEquiv.symm l).2)
    (mulVecUp (Q k) fun r => PolyZonotope.extG S r (finProdFinEquiv.symm l).2)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

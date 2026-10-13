module

public import CORALean.ContSet.PolyZonotope.Float.Operations.ExtG
public import CORALean.ContSet.PolyZonotope.Float.Operations.QuadUp

@[expose] public section

/-!
# `bilin`'s generators, rounded up

`bilinGDown`'s generators rounded the other way, for the gap that `bilinGDiff` charges.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def PolyZonotope.bilinGUp (Q : Fin m → Mat 𝕋 n n) (pZ₁ pZ₂ : PolyZonotope (Vec 𝕋 n)) :
    Mat 𝕋 m ((pZ₁.h + 1) * (pZ₂.h + 1)) :=
  fun k l => PolyZonotope.quadUp (fun r => PolyZonotope.extG pZ₁ r (finProdFinEquiv.symm l).1)
    (mulVecDown (Q k) fun r => PolyZonotope.extG pZ₂ r (finProdFinEquiv.symm l).2)
    (mulVecUp (Q k) fun r => PolyZonotope.extG pZ₂ r (finProdFinEquiv.symm l).2)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

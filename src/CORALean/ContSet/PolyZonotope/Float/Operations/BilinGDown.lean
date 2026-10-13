import CORALean.ContSet.PolyZonotope.Float.Operations.ExtG
import CORALean.ContSet.PolyZonotope.Float.Operations.QuadDown

/-!
# `bilin`'s generators, rounded down

Generator `(i, j)` of the pairing of two sets over the same factors, `Gᵢᵀ Q Gⱼ`, with `Gᵢ` of the
first and `Gⱼ` of the second. `quadMapGDown` is the self-pairing.
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

/-- Generator `(i, j)` of the pairing, rounded down: `Q *ᵥ Gⱼ` in both directions first, then the
outer product against `Gᵢ` over that interval. -/
def PolyZonotope.bilinGDown (Q : Fin m → Mat 𝕋 n n) (pZ₁ pZ₂ : PolyZonotope (Vec 𝕋 n)) :
    Mat 𝕋 m ((pZ₁.h + 1) * (pZ₂.h + 1)) :=
  fun k l => PolyZonotope.quadDown (fun r => PolyZonotope.extG pZ₁ r (finProdFinEquiv.symm l).1)
    (mulVecDown (Q k) fun r => PolyZonotope.extG pZ₂ r (finProdFinEquiv.symm l).2)
    (mulVecUp (Q k) fun r => PolyZonotope.extG pZ₂ r (finProdFinEquiv.symm l).2)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

import CORALean.ContSet.PolyZonotope.Float.Operations.SubsMul

/-!
# `PolyZonotope.subsPow`

CORA's `Y{i,j}` on the stored floats: the `d`-th power of a sum of monomials, by repeated
`subsMul`, the empty product being the term `1`.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {p : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def PolyZonotope.subsPow (A : List ((𝕋 × 𝕋) × (Fin p → ℕ))) :
    ℕ → List ((𝕋 × 𝕋) × (Fin p → ℕ))
  | 0 => [((one, one), 0)]
  | d + 1 => PolyZonotope.subsMul A (PolyZonotope.subsPow A d)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

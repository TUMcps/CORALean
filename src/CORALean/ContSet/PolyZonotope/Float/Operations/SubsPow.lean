module

public import CORALean.ContSet.PolyZonotope.Float.Operations.SubsMul

@[expose] public section

/-!
# `PolyZonotope.subsPow`

CORA's `Y{i,j}` on the stored floats: the `d`-th power of a sum of monomials, by repeated
`subsMul`, the empty product being the term `1`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {p : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def PolyZonotope.subsPow (A : List ((Interval 𝕋) × (Fin p → ℕ))) :
    ℕ → List ((Interval 𝕋) × (Fin p → ℕ))
  | 0 => [(⟨one, one⟩, 0)]
  | d + 1 => PolyZonotope.subsMul A (PolyZonotope.subsPow A d)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

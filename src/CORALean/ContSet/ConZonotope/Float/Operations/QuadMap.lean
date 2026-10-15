module

public import CORALean.ContSet.ConZonotope.Float.Operations.QuadMapDep
public import CORALean.ContSet.ConZonotope.Float.Operations.AbsorbRounding

@[expose] public section

/-!
# `ConZonotope.quadMap`

CORA's `@conZonotope/quadMap` for a single constrained zonotope on the stored floats: the
error box made into coefficients (`absorbRounding`), then `quadMapDep`. The constraints stay on the
linear block of coefficients, the factors that are the old ones, so the squares and products
are free and the result is an outer approximation, never the exact image. CORA's preliminary
`rescale 'iter'` only tightens it and is not modelled.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ConZonotope.quadMap (Q : Fin m → Mat 𝕋 n n) (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) : ConZonotope
    𝕋 (Vec 𝕋 m) :=
  ConZonotope.quadMapDep Q cZ.absorbRounding

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

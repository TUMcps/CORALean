module

public import CORALean.ContSet.ZonoBundle.Float.ZonoBundle
public import CORALean.ContSet.Zonotope.Float.Operations.QuadMapTri

@[expose] public section

/-!
# `ZonoBundle.quadMapCora`

CORA's `zonoBundle`/`quadMap(zB, Q)` with each member mapped by CORA's own `quadMap` of a
zonotope, `Zonotope.quadMapTri`: `N + N(N + 1)/2` generators, the squares then the lower
triangle of `M + Mᵀ`. The members are mapped one by one and the count is unchanged.

## Inputs
* `Q` – quadratic form matrices
* `zB` – float zonotope bundle

## Output
* enclosure of the quadratic image
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       21-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ZonoBundle.quadMapCora (Q : Fin m → Mat 𝕋 n n) (zB : ZonoBundle (Vec 𝕋 n)) :
    ZonoBundle (Vec 𝕋 m) where
  k := zB.k
  Z := fun i => Zonotope.quadMapTri Q (zB.Z i)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

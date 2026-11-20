module

public import CORALean.ContSet.Zonotope.Float.Operations.QuadMapFilter
public import CORALean.ContSet.Zonotope.Float.Operations.QuadMapTri

@[expose] public section

/-!
# `Zonotope.quadMapTriFiltered`, over a floating-point scalar

CORA's `@zonotope/quadMap` of one zonotope as CORA returns it: `quadMapTri`, then CORA's
`nonzeroFilter`, or the box of the generators for at most one nonzero `Q⁽ⁱ⁾` (`quadMapFilter`).

## Inputs
* `Q` – quadratic form per output coordinate
* `Z` – zonotope

## Output
* zonotope enclosing the quadratic image, with CORA's generators
-/

-- Authors:       Claude Opus 5.5
-- Written:       16-November-2026
-- Last update:   20-November-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `quadMap` of a zonotope with its `nonzeroFilter`, or its box for one nonzero output. -/
def Zonotope.quadMapTriFiltered (Q : Fin m → Mat 𝕋 n n) (Z : Zonotope (Vec 𝕋 n)) :
    Zonotope (Vec 𝕋 m) :=
  let Zq := Z.quadMapTri Q                                          -- aux_quadMapSingle
  Zq.quadMapFilter Q                            -- nonzeroFilter(Gquad) or sum(abs(Gquad),2)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

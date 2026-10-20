module

public import CORALean.ContSet.Polygon.Float.Operations.Basic
public import CORALean.ContSet.VPolytope.Float.Operations.EnclosePoints

@[expose] public section

/-!
# `Polygon.minus`, over a floating-point scalar

CORA's `@polygon/minus` with a vector subtrahend, `pgon + (-p)`: the sum with the one-piece
polygon at the point `-p`. `neg` is exact, so the point is stored as given; the sum is
`Polygon.plus`, whose rounding goes into each piece's error box.

## Inputs
* `P` – polygon
* `p` – point of length `2`

## Output
* the sum of `P` with the one-piece polygon at the point `-p`
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

def Polygon.minus (P : Polygon 𝕋) (p : Vec 𝕋 2) : Polygon 𝕋 :=
  let point : VPolytope (Vec 𝕋 2) := VPolytope.enclosePoints fun (_ : Fin 1) i => neg (p i)
  Polygon.plus P (Polygon.ofPieces [point])

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

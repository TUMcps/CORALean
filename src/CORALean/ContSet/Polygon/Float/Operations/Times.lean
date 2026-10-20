module

public import CORALean.ContSet.Polygon.Float.Operations.Basic

@[expose] public section

/-!
# `Polygon.times`, over a floating-point scalar

CORA's `@polygon/times`: `diag(M) * pgon`, so `mtimes` at the float diagonal matrix
`diagonalBlock v`. Not `ContSet.times`: a polygon is fixed at dimension two and has no `Mtimes`
instance.

## Inputs
* `v` – vector of length `2`
* `P` – polygon

## Output
* every piece scaled coordinatewise by `v`: `mtimes` at `diag(v)`
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every piece scaled coordinatewise by `v`: `mtimes` at `diag(v)`. -/
def Polygon.times (v : Vec 𝕋 2) (P : Polygon 𝕋) : Polygon 𝕋 :=
  Polygon.mtimes (diagonalBlock v) P

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

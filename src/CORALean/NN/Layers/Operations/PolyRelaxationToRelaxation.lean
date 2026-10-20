module

public import CORALean.NN.Layers.Definitions.PolyRelaxation
public import CORALean.NN.Layers.Definitions.Relaxation

@[expose] public section

/-!
# An order-1 polynomial relaxation read as an affine one

And back, so nothing distinguishes the two at order 1: the same data, read as a slope and an
offset rather than as two coefficients.

## Inputs
* `P` – order-one polynomial relaxation

## Output
* affine relaxation with the coefficients as slope and offset
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The two coefficients as a slope and an offset. -/
def PolyRelaxation.toRelaxation (P : PolyRelaxation 𝕋 1) : Relaxation 𝕋 where
  slope l u := P.coeffs l u 1
  offset l u := P.coeffs l u 0
  error := P.error

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

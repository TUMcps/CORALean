import CORALean.NN.Layers.Definitions.PolyRelaxation
import CORALean.NN.Layers.Definitions.Relaxation

/-!
# An affine relaxation read as a polynomial one

The affine relaxation is the order-1 case: `offset` and `slope` are the two coefficients, the
constant first, and nothing is rounded — the same stored values, read differently.
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

/-- The same data as two coefficients, constant first. -/
def Relaxation.toPoly (R : Relaxation 𝕋) : PolyRelaxation 𝕋 1 where
  coeffs l u := ![R.offset l u, R.slope l u]
  error := R.error

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

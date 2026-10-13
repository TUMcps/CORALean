import CORALean.NN.Layers.Operations.ConjOffsetHigh
import CORALean.NN.Layers.Operations.ConjOffsetLow

/-!
# The offset an affine conjugate stores

The midpoint of the two roundings of `ra · offset + c`, as for the slope.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The offset chosen: the midpoint of its two roundings. -/
def Relaxation.conjOffset (R : Relaxation 𝕋) (A B : ScaleRounding 𝕋) (c l u : 𝕋) : 𝕋 :=
  half (addUp (Relaxation.conjOffsetLow R A B c l u) (Relaxation.conjOffsetHigh R A B c l u))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

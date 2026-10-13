import CORALean.NN.Layers.Definitions.Relaxation
import CORALean.NN.Layers.Definitions.ScaleRounding

/-!
# An affine conjugate's offset, rounded up

`ra · offset + c`, rounded up, the mirror of `conjOffsetLow`.
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

/-- The upper rounding of `ra * R.offset + c`. -/
def Relaxation.conjOffsetHigh (R : Relaxation 𝕋) (A B : ScaleRounding 𝕋) (c l u : 𝕋) : 𝕋 :=
  addUp (A.up (R.offset (B.down l) (B.up u))) c

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

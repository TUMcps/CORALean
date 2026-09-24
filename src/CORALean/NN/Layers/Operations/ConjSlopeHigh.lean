import CORALean.NN.Layers.Definitions.Relaxation
import CORALean.NN.Layers.Definitions.ScaleRounding

/-!
# An affine conjugate's slope, rounded up

The upper rounding of `ra · rb · λ`, the mirror of `conjSlopeLow`.
-/

-- Authors:       Tobias Ladner
-- Written:       03-September-2026
-- Last update:   23-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The upper rounding of `ra * rb * R.slope`, `rb`'s box map folded in first. -/
def Relaxation.conjSlopeHigh (R : Relaxation 𝕋) (A B : ScaleRounding 𝕋) (l u : 𝕋) : 𝕋 :=
  A.up (B.up (R.slope (B.down l) (B.up u)))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

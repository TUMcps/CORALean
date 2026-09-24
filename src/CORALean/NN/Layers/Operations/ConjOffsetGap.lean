import CORALean.NN.Layers.Operations.ConjOffset

/-!
# How far a stored conjugate offset may be from the exact one

The offset's counterpart of `conjSlopeGap`.
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

/-- The distance from the stored offset to the further rounding, rounded up. -/
def Relaxation.conjOffsetGap (R : Relaxation 𝕋) (A B : ScaleRounding 𝕋) (c l u : 𝕋) : 𝕋 :=
  maximum (subUp (Relaxation.conjOffsetHigh R A B c l u) (Relaxation.conjOffset R A B c l u))
    (subUp (Relaxation.conjOffset R A B c l u) (Relaxation.conjOffsetLow R A B c l u))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

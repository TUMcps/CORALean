import CORALean.NN.Layers.Operations.ConjOffsetGap
import CORALean.NN.Layers.Operations.ConjSlopeGap
import CORALean.NN.Layers.Operations.ConjTBound

/-!
# The error an affine conjugate stores

`ra`'s rounding of `f`'s own error, plus the slope gap charged against a bound on `t`, plus
the offset gap, all rounded up. At exact scalings both gaps vanish and this is `ra` times `f`'s
error, which is all the transport costs over ℝ.
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

/-- `ra`'s error, plus the slope gap charged against `|t|`, plus the offset gap. -/
def Relaxation.conjError (R : Relaxation 𝕋) (A B : ScaleRounding 𝕋) (c l u : 𝕋) : 𝕋 :=
  addUp (addUp (A.up (R.error (B.down l) (B.up u)))
    (mulUp (Relaxation.conjSlopeGap R A B l u) (Relaxation.conjTBound l u)))
    (Relaxation.conjOffsetGap R A B c l u)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

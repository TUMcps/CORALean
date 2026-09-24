import CORALean.NN.Layers.Operations.ConjSlopeHigh
import CORALean.NN.Layers.Operations.ConjSlopeLow

/-!
# The slope an affine conjugate stores

The midpoint of the interval either rounding of `ra · rb · λ` could land in, exactly as
`curvMid` picks one: any value there would do, the error being measured from it.
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

/-- The slope chosen: the midpoint of its two roundings. -/
def Relaxation.conjSlope (R : Relaxation 𝕋) (A B : ScaleRounding 𝕋) (l u : 𝕋) : 𝕋 :=
  half (addUp (Relaxation.conjSlopeLow R A B l u) (Relaxation.conjSlopeHigh R A B l u))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

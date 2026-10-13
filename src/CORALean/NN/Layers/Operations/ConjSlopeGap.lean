import CORALean.NN.Layers.Operations.ConjSlope

/-!
# How far a stored conjugate slope may be from the exact one

The distance from the stored midpoint to the further of the two roundings, rounded up: the
slope's share of what storing one value rather than the exact product costs.
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

/-- The distance from the stored slope to the further rounding, rounded up. -/
def Relaxation.conjSlopeGap (R : Relaxation 𝕋) (A B : ScaleRounding 𝕋) (l u : 𝕋) : 𝕋 :=
  maximum (subUp (Relaxation.conjSlopeHigh R A B l u) (Relaxation.conjSlope R A B l u))
    (subUp (Relaxation.conjSlope R A B l u) (Relaxation.conjSlopeLow R A B l u))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

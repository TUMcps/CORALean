import CORALean.NN.Layers.Operations.SigmoidDerivHi
import CORALean.NN.Layers.Operations.SigmoidDerivLo

/-!
# The sigmoid slope

The secant, clamped into the derivative bracket. The secant is a guess and nothing more: the
width may round to zero, where `divUp` bounds nothing, and the clamp makes that harmless — any
slope in the bracket is sound.
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

/-- The secant, clamped into the derivative bracket. -/
def sigmoidSlope (E : Enclosure 𝕋) (l u : 𝕋) : 𝕋 :=
  maximum (sigmoidDerivLo E l u)
    (minimum (sigmoidDerivHi E l u) (divUp (subUp (E.hi u) (E.lo l)) (subDown u l)))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

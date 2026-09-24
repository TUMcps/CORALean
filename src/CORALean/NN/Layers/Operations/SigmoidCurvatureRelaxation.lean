import CORALean.NN.Layers.Operations.RelaxationOfDeriv
import CORALean.NN.Layers.Operations.SigmoidSlope

/-!
# The sigmoid relaxation from its derivative bracket

`Relaxation.ofDeriv` at the sigmoid's derivative bracket and its clamped secant, `σ` at the
box's left end supplied by the same enclosure.
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

def sigmoidCurvatureRelaxation (E : Enclosure 𝕋) : Relaxation 𝕋 :=
  Relaxation.ofDeriv E (sigmoidDerivLo E) (sigmoidDerivHi E) (sigmoidSlope E)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

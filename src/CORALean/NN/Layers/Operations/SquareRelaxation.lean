import CORALean.NN.Layers.Operations.RelaxationOfDeriv
import CORALean.NN.Layers.Operations.SquareEnclosure
import CORALean.NN.Layers.Operations.SquareSlope

/-!
# The square relaxation

`x ↦ x²` is not monotone, so its relaxation is the one a derivative bracket buys,
`Relaxation.ofDeriv`: `σ' x = 2x` lies in `[2l, 2u]` over the box and the slope is the chord's.
The error is quadratic in the width of the box.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The relaxation a bracket of `2x` buys. -/
def squareRelaxation : Relaxation 𝕋 :=
  Relaxation.ofDeriv squareEnclosure squareDerivLo squareDerivHi squareSlope

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

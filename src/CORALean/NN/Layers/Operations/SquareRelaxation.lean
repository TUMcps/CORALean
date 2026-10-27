module

public import CORALean.NN.Layers.Operations.Basic
public import CORALean.NN.Layers.Operations.RelaxationOfDeriv
public import CORALean.Global.StepOf

@[expose] public section

/-!
# The square relaxation

`x ↦ x²` is not monotone, so its relaxation is the one a derivative bracket buys,
`Relaxation.ofDeriv`: `σ' x = 2x` lies in `[2l, 2u]` over the box and the slope is the chord's.
The error is quadratic in the width of the box.

## Inputs
* none

## Output
* relaxation of the square from a bracket of its derivative
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- The chord's slope `l + u`, clamped into the bracket. -/
@[step_of squareRelaxation]
def step_squareSlope (l u : 𝕋) : 𝕋 :=
  maximum (squareDerivLo l u) (minimum (squareDerivHi l u) (addDown l u))


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The relaxation a bracket of `2x` buys. -/
def squareRelaxation : Relaxation 𝕋 :=
  Relaxation.ofDeriv squareEnclosure squareDerivLo squareDerivHi step_squareSlope

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

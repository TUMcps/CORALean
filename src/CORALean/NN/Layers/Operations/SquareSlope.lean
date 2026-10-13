module

public import CORALean.NN.Layers.Operations.SquareDerivLo
public import CORALean.NN.Layers.Operations.SquareDerivHi

@[expose] public section

/-!
# The slope of the square relaxation

The chord's slope `l + u`, clamped into the derivative's bracket so that `Relaxation.ofDeriv`'s
requirement on the slope holds whatever the rounding does.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The chord's slope `l + u`, clamped into the bracket. -/
def squareSlope (l u : 𝕋) : 𝕋 :=
  maximum (squareDerivLo l u) (minimum (squareDerivHi l u) (addDown l u))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

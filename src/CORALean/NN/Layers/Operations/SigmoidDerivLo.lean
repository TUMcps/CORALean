module

public import CORALean.NN.Layers.Definitions.Enclosure

@[expose] public section

/-!
# The sigmoid derivative's lower bound over a box

`σ'` is a product of two sigmoids, each monotone and positive, so the enclosure at the box's
ends brackets it with no case on sign — the lower factors floored at zero, which rounding could
otherwise push below it — and the product rounds down.

## Inputs
* `E` – enclosure of the sigmoid
* `l` – lower end of the box
* `u` – upper end of the box

## Output
* lower bound of the sigmoid's derivative over the box
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

/-- `σ l · σ(-u)` from below, each factor floored at zero. -/
def sigmoidDerivLo (E : Enclosure 𝕋) (l u : 𝕋) : 𝕋 :=
  mulDown (maximum zero (E.lo l)) (maximum zero (E.lo (neg u)))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

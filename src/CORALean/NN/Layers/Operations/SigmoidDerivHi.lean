module

public import CORALean.NN.Layers.Definitions.Enclosure

@[expose] public section

/-!
# The sigmoid derivative's upper bound over a box

`σ u · σ(-l)` from above, the product rounding up; an upper bound on a positive value is
positive, so this side needs no floor.

## Inputs
* `E` – enclosure of the sigmoid
* `l` – lower end of the box
* `u` – upper end of the box

## Output
* upper bound of the sigmoid's derivative over the box
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

/-- `σ u · σ(-l)` from above. -/
def sigmoidDerivHi (E : Enclosure 𝕋) (l u : 𝕋) : 𝕋 :=
  mulUp (E.hi u) (E.hi (neg l))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

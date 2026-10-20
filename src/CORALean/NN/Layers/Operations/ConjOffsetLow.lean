module

public import CORALean.NN.Layers.Definitions.Relaxation
public import CORALean.NN.Layers.Definitions.ScaleRounding

@[expose] public section

/-!
# An affine conjugate's offset, rounded down

`ra · offset + c`, rounded down. Addition needs no sign hypothesis, so this holds for any
`ra`.

## Inputs
* `R` – relaxation of the activation
* `A` – rounding of the output scale
* `B` – rounding of the input scale
* `c` – output shift
* `l` – lower end of the box
* `u` – upper end of the box

## Output
* offset of the affine conjugate, rounded down
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

/-- The lower rounding of `ra * R.offset + c`. -/
def Relaxation.conjOffsetLow (R : Relaxation 𝕋) (A B : ScaleRounding 𝕋) (c l u : 𝕋) : 𝕋 :=
  addDown (A.down (R.offset (B.down l) (B.up u))) c

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

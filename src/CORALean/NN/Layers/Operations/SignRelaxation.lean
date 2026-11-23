module

public import CORALean.NN.Layers.Operations.SignEnclosure
public import CORALean.NN.Layers.Operations.RelaxationOfMonotone

@[expose] public section

/-!
# The sign relaxation

`Relaxation.ofMonotone` at `signEnclosure`: slope zero, the offset the middle of the signs of the
ends and the error half their distance. CORA.cpp's line of a sign layer (binarized networks, no
CORA layer): slope 0, offset `(sign l + sign u) / 2`, radius `(sign u - sign l) / 2`; the values
are halves, so every operation is exact and the two agree bit for bit.

## Inputs
* none

## Output
* slope-zero relaxation of the sign
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The slope-zero relaxation of the sign. -/
def signRelaxation : Relaxation 𝕋 := Relaxation.ofMonotone signEnclosure

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

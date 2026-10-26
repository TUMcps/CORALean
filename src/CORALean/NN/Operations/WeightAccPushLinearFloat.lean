module

public import CORALean.NN.Definitions.WeightAccFloat
public import CORALean.ContSet.Interval.Float.Operations.MatMul
public import CORALean.ContSet.Interval.Float.Operations.MtimesIntervalMat
public import CORALean.ContSet.Interval.Float.Operations.Basic

@[expose] public section

/-!
# `WeightAcc.pushLinear` in floats
CORA's `W = layer.W * W; b = layer.W * b + layer.b` on boxes: the product of the two weight boxes
by `Interval.matMul` and the image of the offset box by `Interval.mtimesIntervalMat`, both
outward-rounded, plus the layer's offset box. Nothing fused yet takes the layer as it is.

## Inputs
* none

## Output
* float accumulator after the linear layer
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n d m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def WeightAcc.pushLinear :
    WeightAcc 𝕋 n d → Interval (Mat 𝕋 m d) → Interval (Vec 𝕋 m) → WeightAcc 𝕋 n m
  | .id, W₂, b₂ => .aff W₂ b₂
  | .aff W b, W₂, b₂ =>
    .aff (Interval.matMul W₂ W) (Interval.plus (Interval.mtimesIntervalMat W₂ b) b₂)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

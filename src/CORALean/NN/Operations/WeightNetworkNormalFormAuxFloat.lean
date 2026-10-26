module

public import CORALean.NN.Definitions.WeightNetworkFloat
public import CORALean.NN.Operations.WeightAccPushLinearFloat
public import CORALean.NN.Operations.WeightAccPushAffineFloat
public import CORALean.NN.Operations.WeightAccLayerFloat

@[expose] public section

/-!
# The loop of `getNormalForm` in floats
The float counterpart of `WeightNetwork.normalFormAux`: a linear layer and an elementwise affine
layer are folded into the accumulator by `WeightAcc.pushLinear` and `WeightAcc.pushAffine`, an
identity layer is dropped, and an activation flushes the accumulator as one layer and restarts.

## Inputs
* none

## Output
* float network over the layers still to come, started from the accumulator
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n m k d : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def WeightNetwork.normalFormAux : ∀ {n d k : ℕ}, WeightAcc 𝕋 n d → WeightNetwork 𝕋 d k →
    WeightNetwork 𝕋 n k
  | _, _, _, .id, .nil => .nil
  | _, _, _, .aff W b, .nil => .cons (.linear W b) .nil
  | _, _, _, acc, .cons (.linear W b) rest => normalFormAux (acc.pushLinear W b) rest
  | _, _, _, acc, .cons (.elementwiseAffine s o) rest => normalFormAux (acc.pushAffine s o) rest
  | _, _, _, acc, .cons .identity rest => normalFormAux acc rest
  | _, _, _, acc, .cons (.activation f) rest =>
    .cons acc.layer (.cons (.activation f) (normalFormAux .id rest))  -- flush, then restart

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

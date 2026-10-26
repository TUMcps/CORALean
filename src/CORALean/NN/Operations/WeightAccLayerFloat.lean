module

public import CORALean.NN.Definitions.WeightAccFloat
public import CORALean.NN.Definitions.WeightLayerFloat

@[expose] public section

/-!
# The float layer emitted for the accumulated map
The float counterpart of `WeightAcc.layer`: the identity for nothing fused, the linear layer of the
fused boxes otherwise.

## Inputs
* none

## Output
* float layer of the accumulated map
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n d : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def WeightAcc.layer : WeightAcc 𝕋 n d → WeightLayer 𝕋 n d
  | .id => .identity
  | .aff W b => .linear W b

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.NN.Operations.WeightNetworkNormalFormAuxFloat

@[expose] public section

/-!
# `getNormalForm` of a float network
CORA's `getNormalForm` in floats: the layers fused into the fewest linear layers between the
activations, as `WeightNetwork.normalForm`, every product of weights rounded outward into a box.

## Inputs
* `N` – float weight network

## Output
* float network of the fused layers
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n k : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def WeightNetwork.normalForm (N : WeightNetwork 𝕋 n k) : WeightNetwork 𝕋 n k :=
  N.normalFormAux .id

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

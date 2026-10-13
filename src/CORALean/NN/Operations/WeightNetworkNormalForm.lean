module

public import CORALean.NN.Operations.WeightNetworkNormalFormAux

@[expose] public section

/-!
# `neuralNetwork.getNormalForm`

CORA's `getNormalForm`: the network with consecutive affine layers fused, `W = W₂ W₁` and
`b = W₂ b₁ + b₂`, so that linear layers and activations alternate. Not modelled: CORA's early
return for a network already in that form, which computes the same function.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {α : Type} [Semiring α] {n m k d : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The fused network, started from nothing accumulated. -/
def WeightNetwork.normalForm (N : WeightNetwork α n k) : WeightNetwork α n k :=
  N.normalFormAux .id

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

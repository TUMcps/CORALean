module

public import CORALean.NN.Definitions.ActivationKind

@[expose] public section

/-!
# `nnActivationLayer.getMergeBuckets`

CORA's `getMergeBuckets`: `f([-inf, inf])` without the infinite entries, the finite limits of the
activation, which are the values its neurons are merged at: `{0}` for ReLU, `{0, 1}` for the
logistic function and `{-1, 1}` for tanh. Integers, since they are exact there.

## Inputs
* none

## Output
* finite limits of the activation at minus and plus infinity
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The finite limits of `f` at `-∞` and `+∞`. -/
def ActivationKind.mergeValues : ActivationKind → List ℤ
  | .relu => [0]
  | .sigmoid => [0, 1]
  | .tanh => [-1, 1]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

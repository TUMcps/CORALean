module

public import CORALean.NN.Definitions.SmoothNetwork
public import CORALean.NN.Layers.Definitions.Relu
public import CORALean.NN.Layers.Definitions.Sigmoid
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

@[expose] public section

/-!
# What a `SmoothNetwork` computes

CORA's `evaluate` on a point: the layers' maps composed, first layer first. The same maps as the
`eval` of the `Enclose` instances of the corresponding kinds (`LinearLayer`, `TanhLayer`,
`ReluLayer`, `SigmoidLayer`).

## Inputs
* none

## Output
* function the smooth network computes
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def SmoothNetwork.eval : ∀ {n k : ℕ}, SmoothNetwork n k → Vec ℝ n → Vec ℝ k
  | _, _, .output, x => x
  | _, _, .linear W b rest, x => rest.eval (W *ᵥ x + b)
  | _, _, .elementwiseAffine scale offset rest, x => rest.eval fun i => scale i * x i + offset i
  | _, _, .tanh rest, x => rest.eval fun i => Real.tanh (x i)
  | _, _, .relu rest, x => rest.eval fun i => Real.relu (x i)
  | _, _, .sigmoid rest, x => rest.eval fun i => Real.sigmoid (x i)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.NN.Layers.Operations.Relu
public import CORALean.NN.Layers.Theorems.ActivationTracks
public import CORALean.NN.Layers.Theorems.ReluRelaxationEncloses

@[expose] public section

/-!
# The ReLU layer keeps the generators of a zonotope in front

ReLU coordinatewise, at every slope: `reluRelaxation_encloses` read through the activation
layer's own tracking.

## Inputs
* `lam` – slope choice for each box

## Hypotheses
* none

## Conclusion
* the layer tracks ReLU coordinatewise
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       13-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float
open scoped CORALean.Float

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Layer.relu_tracks (lam : 𝕋 → 𝕋 → 𝕋) :
    (Layer.relu (S := 𝒵[𝕋]) (n := n) lam).Tracks fun x i => Real.relu (x i) :=
  Layer.activation_tracks (reluRelaxation_encloses lam)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

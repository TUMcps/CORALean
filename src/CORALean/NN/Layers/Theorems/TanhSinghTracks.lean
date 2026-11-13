module

public import CORALean.NN.Layers.Operations.TanhSingh
public import CORALean.NN.Layers.Theorems.ActivationTracks
public import CORALean.NN.Layers.Theorems.TanhSinghRelaxationEncloses

@[expose] public section

/-!
# The tanh layer by Singh's transformer keeps the generators in front

`Layer.activation_tracks` at the relaxation of the tanh layer by Singh's transformer,
whose soundness is `tanhSinghRelaxation_encloses`.

## Inputs
* `k` – reduction depth of the exponential

## Hypotheses
* none

## Conclusion
* the layer tracks `Real.tanh` coordinatewise
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

theorem Layer.tanhSingh_tracks (k : ℕ) :
    (Layer.tanhSingh (𝕋 := 𝕋) (S := 𝒵[𝕋]) (n := n) k).Tracks fun x i => Real.tanh (x i) :=
  Layer.activation_tracks (tanhSinghRelaxation_encloses k)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

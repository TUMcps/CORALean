module

public import CORALean.NN.Layers.Operations.TanhRegression
public import CORALean.NN.Layers.Theorems.ActivationTracks
public import CORALean.NN.Layers.Theorems.TanhRegressionRelaxationEncloses

@[expose] public section

/-!
# The tanh layer at the regression line keeps the generators in front

`Layer.activation_tracks` at the relaxation of the tanh layer at the regression line,
whose soundness is `tanhRegressionRelaxation_encloses`.

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

theorem Layer.tanhRegression_tracks (k : ℕ) :
    (Layer.tanhRegression (𝕋 := 𝕋) (S := 𝒵[𝕋]) (n := n) k).Tracks fun x i => Real.tanh (x i) :=
  Layer.activation_tracks (tanhRegressionRelaxation_encloses k)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

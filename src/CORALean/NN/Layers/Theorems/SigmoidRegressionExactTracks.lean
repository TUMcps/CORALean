module

public import CORALean.NN.Layers.Operations.SigmoidRegressionExact
public import CORALean.NN.Layers.Theorems.ActivationTracks
public import CORALean.NN.Layers.Theorems.SigmoidRegressionExactRelaxationEncloses

@[expose] public section

/-!
# The sigmoid layer at the regression line, with the exact error, keeps the generators in front

`Layer.activation_tracks` at the exact-error regression relaxation of the sigmoid, whose
soundness is `sigmoidRegressionExactRelaxation_encloses`.

## Inputs
* `k` – reduction depth of the exponential

## Hypotheses
* none

## Conclusion
* the layer tracks `Real.sigmoid` coordinatewise
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

theorem Layer.sigmoidRegressionExact_tracks (k : ℕ) :
    (Layer.sigmoidRegressionExact (𝕋 := 𝕋) (S := 𝒵[𝕋]) (n := n) k).Tracks
      fun x i => Real.sigmoid (x i) :=
  Layer.activation_tracks (sigmoidRegressionExactRelaxation_encloses k)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

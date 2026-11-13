module

public import CORALean.NN.Layers.Operations.TanhRegressionExact
public import CORALean.NN.Layers.Theorems.ActivationTracks
public import CORALean.NN.Layers.Theorems.SigmoidRegressionExactRelaxationEncloses
public import CORALean.NN.Layers.Theorems.OfAffineConjEncloses
public import CORALean.NN.Layers.Theorems.Basic

@[expose] public section

/-!
# The tanh layer at the regression line, with the exact error, keeps the generators in front

`Layer.activation_tracks` at the sigmoid's exact-error regression relaxation transported along
`tanh t = 2 σ(2 t) - 1`, the relaxation of `tanhRegressionExact_encloses`.

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
open ContSet ContSetLike Float.SoundFloatArithmetic

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The sigmoid relaxation's soundness, transported along the conjugation identity. -/
private theorem aux_step_tanhRegressionExactRelaxation_encloses (k : ℕ) :
    (step_tanhRegressionExactRelaxation (𝕋 := 𝕋) k).Encloses Real.tanh :=
  Relaxation.ofAffineConj_encloses (sigmoidRegressionExactRelaxation_encloses k)
    doubleRounding_encloses doubleRounding_encloses (by norm_num) (by norm_num)
    (fun t => by rw [toReal_neg, toReal_one, Real.tanh_eq_sigmoid]; ring)


-- =======================================  MAIN THEOREM  ======================================= --

theorem Layer.tanhRegressionExact_tracks (k : ℕ) :
    (Layer.tanhRegressionExact (𝕋 := 𝕋) (S := 𝒵[𝕋]) (n := n) k).Tracks
      fun x i => Real.tanh (x i) :=
  Layer.activation_tracks (aux_step_tanhRegressionExactRelaxation_encloses k)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

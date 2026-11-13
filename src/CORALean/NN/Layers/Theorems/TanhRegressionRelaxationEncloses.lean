module

public import CORALean.NN.Layers.Operations.TanhRegression
public import CORALean.NN.Layers.Theorems.SigmoidRegressionRelaxationEncloses
public import CORALean.NN.Layers.Theorems.Basic
public import CORALean.NN.Layers.Theorems.OfAffineConjEncloses

@[expose] public section

/-!
# The tanh relaxation at the regression line is sound

The sigmoid's relaxation at the regression line, transported along the conjugation
identity `tanh t = 2 σ(2 t) - 1`, as for `tanhRelaxation`.

## Inputs
* `k` – reduction depth of the exponential

## Hypotheses
* none

## Conclusion
* the relaxation is sound for `Real.tanh`
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       13-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float.SoundFloatArithmetic

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem tanhRegressionRelaxation_encloses (k : ℕ) :
    (step_tanhRegressionRelaxation (𝕋 := 𝕋) k).Encloses Real.tanh :=
  Relaxation.ofAffineConj_encloses (sigmoidRegressionRelaxation_encloses k) doubleRounding_encloses
    doubleRounding_encloses (by norm_num) (by norm_num)
    (fun t => by rw [toReal_neg, toReal_one, Real.tanh_eq_sigmoid]; ring)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

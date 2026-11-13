module

public import CORALean.NN.Layers.Operations.TanhSingh
public import CORALean.NN.Layers.Theorems.SigmoidSinghRelaxationEncloses
public import CORALean.NN.Layers.Theorems.Basic
public import CORALean.NN.Layers.Theorems.OfAffineConjEncloses

@[expose] public section

/-!
# The tanh relaxation by Singh's transformer is sound

The sigmoid's relaxation by Singh's transformer, transported along the conjugation
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

theorem tanhSinghRelaxation_encloses (k : ℕ) :
    (step_tanhSinghRelaxation (𝕋 := 𝕋) k).Encloses Real.tanh :=
  Relaxation.ofAffineConj_encloses (sigmoidSinghRelaxation_encloses k) doubleRounding_encloses
    doubleRounding_encloses (by norm_num) (by norm_num)
    (fun t => by rw [toReal_neg, toReal_one, Real.tanh_eq_sigmoid]; ring)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

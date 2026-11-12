module

public import CORALean.NN.Layers.Operations.TanhSingh
public import CORALean.NN.Layers.Theorems.SigmoidSinghRelaxationEncloses
public import CORALean.NN.Layers.Theorems.OfAffineConjEncloses
public import CORALean.NN.Layers.Theorems.Basic

@[expose] public section

/-!
# The tanh layer by Singh's transformer is sound

`Layer.activation_encloses` at the relaxation by Singh's transformer. Tanh's is the sigmoid's
transported along `tanh t = 2 σ(2 t) - 1`, as for `tanhRelaxation`.

## Inputs
* `k` – reduction depth of the exponential

## Hypotheses
* none

## Conclusion
* the layer is sound for `Real.tanh` coordinatewise
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       12-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet ContSetLike Float.SoundFloatArithmetic

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋]
  {S : ℕ → Type} [∀ n, ContSetLike (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat 𝕋) S] [Float.IntervalOuter S 𝕋] [Float.OfInterval S 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The sigmoid relaxation's soundness, transported along the conjugation identity. -/
private theorem aux_step_tanhSinghRelaxation_encloses (k : ℕ) :
    (step_tanhSinghRelaxation (𝕋 := 𝕋) k).Encloses Real.tanh :=
  Relaxation.ofAffineConj_encloses (sigmoidSinghRelaxation_encloses k) doubleRounding_encloses
    doubleRounding_encloses (by norm_num) (by norm_num)
    (fun t => by rw [toReal_neg, toReal_one, Real.tanh_eq_sigmoid]; ring)


-- =======================================  MAIN THEOREM  ======================================= --

/-- `Real.tanh` coordinatewise, at every reduction depth. -/
theorem Layer.tanhSingh_encloses (k : ℕ) :
    (Layer.tanhSingh (𝕋 := 𝕋) (S := S) (n := n) k).Encloses fun x i => Real.tanh (x i) :=
  Layer.activation_encloses (aux_step_tanhSinghRelaxation_encloses k)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

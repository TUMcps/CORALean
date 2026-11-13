module

public import CORALean.NN.Layers.Operations.TanhRegressionExact
public import CORALean.NN.Layers.Theorems.SigmoidRegressionExactRelaxationEncloses
public import CORALean.NN.Layers.Theorems.OfAffineConjEncloses
public import CORALean.NN.Layers.Theorems.Basic

@[expose] public section

/-!
# The tanh layer at the regression line, with the exact error, is sound

`Layer.activation_encloses` at the sigmoid's exact-error regression relaxation transported along
`tanh t = 2 σ(2 t) - 1`, as for `tanhRelaxation`.

## Inputs
* `k` – reduction depth of the exponential

## Hypotheses
* none

## Conclusion
* the layer is sound for `Real.tanh` coordinatewise
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       13-November-2026
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
private theorem aux_step_tanhRegressionExactRelaxation_encloses (k : ℕ) :
    (step_tanhRegressionExactRelaxation (𝕋 := 𝕋) k).Encloses Real.tanh :=
  Relaxation.ofAffineConj_encloses (sigmoidRegressionExactRelaxation_encloses k)
    doubleRounding_encloses doubleRounding_encloses (by norm_num) (by norm_num)
    (fun t => by rw [toReal_neg, toReal_one, Real.tanh_eq_sigmoid]; ring)


-- =======================================  MAIN THEOREM  ======================================= --

/-- `Real.tanh` coordinatewise, at every reduction depth. -/
theorem Layer.tanhRegressionExact_encloses (k : ℕ) :
    (Layer.tanhRegressionExact (𝕋 := 𝕋) (S := S) (n := n) k).Encloses fun x i => Real.tanh (x i) :=
  Layer.activation_encloses (aux_step_tanhRegressionExactRelaxation_encloses k)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

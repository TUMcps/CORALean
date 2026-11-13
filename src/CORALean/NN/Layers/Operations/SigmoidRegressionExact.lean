module

public import CORALean.NN.Layers.Operations.Activation
public import CORALean.NN.Layers.Operations.SigmoidRegressionExactRelaxation

@[expose] public section

/-!
# The sigmoid layer at the regression line, with the exact error

CORA's `nnSigmoidLayer` at its default `poly_method = 'regression'`: `Layer.activation` at
`sigmoidRegressionExactRelaxation k`, whose error is that of the extremum of `σ t - m t`.

## Inputs
* `k` – reduction depth of the exponential

## Output
* layer applying the relaxation to every neuron
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       13-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet ContSetLike

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋]
  {S : ℕ → Type} [∀ n, ContSetLike (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat 𝕋) S] [Float.IntervalOuter S 𝕋] [Float.OfInterval S 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The sigmoid layer at the regression line, with the exact error. -/
def Layer.sigmoidRegressionExact (k : ℕ) : Layer S n n :=
  Layer.activation (sigmoidRegressionExactRelaxation k)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

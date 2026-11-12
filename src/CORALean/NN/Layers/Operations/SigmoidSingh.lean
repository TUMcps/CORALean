module

public import CORALean.NN.Layers.Operations.Activation
public import CORALean.NN.Layers.Operations.SigmoidSinghRelaxation

@[expose] public section

/-!
# The sigmoid layer by Singh's transformer

CORA's `nnSigmoidLayer` at `poly_method = 'singh'`: `Layer.activation` at
`sigmoidSinghRelaxation k`. `Layer.sigmoid` is the tighter relaxation; this is what CORA computes.

## Inputs
* `k` – reduction depth of the exponential

## Output
* layer applying the relaxation to every neuron
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       12-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet ContSetLike

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋]
  {S : ℕ → Type} [∀ n, ContSetLike (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat 𝕋) S] [Float.IntervalOuter S 𝕋] [Float.OfInterval S 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The sigmoid layer at Singh's slope. -/
def Layer.sigmoidSingh (k : ℕ) : Layer S n n := Layer.activation (sigmoidSinghRelaxation k)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

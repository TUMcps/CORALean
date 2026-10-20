module

public import CORALean.NN.Layers.Operations.Activation
public import CORALean.NN.Layers.Operations.TanhRelaxation

@[expose] public section

/-!
# The tanh layer

CORA's `nnTanhLayer`: `Layer.activation` at `tanhRelaxation k`, the sigmoid relaxation
transported; `k` is the reduction depth the sigmoid underneath is built at.

## Inputs
* `k` – reduction depth of the exponential

## Output
* layer applying the tanh relaxation to every neuron
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋]
  {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat 𝕋) S] [Float.IntervalOuter S 𝕋] [Float.OfInterval S 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Layer.tanh (k : ℕ) : Layer S n n := Layer.activation (tanhRelaxation k)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

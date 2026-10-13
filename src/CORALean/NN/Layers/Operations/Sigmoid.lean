module

public import CORALean.NN.Layers.Operations.Activation
public import CORALean.NN.Layers.Operations.SigmoidRelaxation

@[expose] public section

/-!
# The sigmoid layer

CORA's `nnSigmoidLayer`: `Layer.activation` at `sigmoidRelaxation k`. `k` is the exponential's
reduction depth: every `k` is sound, a larger one tighter, and it reaches both the value and
the derivative bracket.
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

def Layer.sigmoid (k : ℕ) : Layer S n n := Layer.activation (sigmoidRelaxation k)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

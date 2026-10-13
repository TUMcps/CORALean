module

public import CORALean.NN.Layers.Operations.Activation
public import CORALean.NN.Layers.Operations.LeakyReluRelaxation
public import CORALean.NN.Layers.Operations.LeakyReluSlope

@[expose] public section

/-!
# The leaky ReLU layer

CORA's `nnLeakyReLULayer`: `Layer.activation` at `leakyReluRelaxation α lam`, the slope
`leakyReluSlope α` unless the caller names another. `α` is CORA's `alpha`, `0.01` by default.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋]
  {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat 𝕋) S] [Float.IntervalOuter S 𝕋] [Float.OfInterval S 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Layer.leakyRelu (α : 𝕋) (lam : 𝕋 → 𝕋 → 𝕋 := leakyReluSlope α) : Layer S n n :=
  Layer.activation (leakyReluRelaxation α lam)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

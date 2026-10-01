import CORALean.NN.Layers.Operations.Activation
import CORALean.NN.Layers.Operations.LeakyReluRelaxation
import CORALean.NN.Layers.Operations.LeakyReluSlope

/-!
# The leaky ReLU layer

CORA's `nnLeakyReLULayer`: `Layer.activation` at `leakyReluRelaxation α lam`, the slope
`leakyReluSlope α` unless the caller names another. `α` is CORA's `alpha`, `0.01` by default.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


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

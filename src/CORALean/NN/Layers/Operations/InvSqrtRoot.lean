import CORALean.NN.Layers.Operations.Activation
import CORALean.NN.Layers.Operations.InvSqrtRootRelaxation

/-!
# The inverse square root layer

CORA's `nnInvSqrtRootLayer`: `Layer.activation` at `invSqrtRootRelaxation p`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋]
  {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat 𝕋) S] [Float.IntervalOuter S 𝕋] [Float.OfInterval S 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Layer.invSqrtRoot (p : ℕ) : Layer S n n := Layer.activation (invSqrtRootRelaxation p)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

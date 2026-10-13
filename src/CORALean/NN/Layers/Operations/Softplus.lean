module

public import CORALean.NN.Layers.Operations.Activation
public import CORALean.NN.Layers.Operations.SoftplusRelaxation

@[expose] public section

/-!
# The softplus layer

CORA's `nnSoftPlusLayer`: `Layer.activation` at `softplusRelaxation β k nl kl`, the sharpness `β`
stored in the scalar.
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

def Layer.softplus (β : 𝕋) (k nl kl : ℕ) : Layer S n n :=
  Layer.activation (softplusRelaxation β k nl kl)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

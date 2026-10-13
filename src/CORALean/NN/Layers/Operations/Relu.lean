module

public import CORALean.NN.Layers.Operations.Activation
public import CORALean.NN.Layers.Operations.ReluRelaxation
public import CORALean.NN.Layers.Operations.ReluSlope

@[expose] public section

/-!
# The ReLU layer

CORA's `nnReLULayer`: `Layer.activation` at `reluRelaxation`, the slope `reluSlope` unless the
caller names another. The one standard activation that needs no transcendental function, and
the one carrying a nonzero slope.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋]
  {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat 𝕋) S] [Float.IntervalOuter S 𝕋] [Float.OfInterval S 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Layer.relu (lam : 𝕋 → 𝕋 → 𝕋 := reluSlope) : Layer S n n :=
  Layer.activation (reluRelaxation lam)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

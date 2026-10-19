module

public import CORALean.NN.Layers.Operations.Activation
public import CORALean.NN.Layers.Operations.ReluRelaxation
public import CORALean.NN.Layers.Operations.ReluSlope

@[expose] public section

/-!
# The ReLU layer

CORA's `nnReLULayer`: `Layer.activation` at `reluRelaxation`. Only the slope rule `lam` is
passed, not the function itself, and not a pair of function and relaxation. A `Layer` stores
`enclose` alone, as every layer does (`Layer.sigmoid k` takes the exponential's depth `k` and
builds its `sigmoidRelaxation`, and no function, the same way): the exact function ReLU is not
data of the layer but the `f` that `Layer.Encloses` relates it to, stated by
`Layer.relu_encloses`. The relaxation is what the layer computes with, so it is what the layer is
built from; the slope `lam` is the one choice ReLU leaves open.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   23-September-2026
-- Reviewed:      19-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋]
  {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat 𝕋) S] [Float.IntervalOuter S 𝕋] [Float.OfInterval S 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `Layer.activation` at `reluRelaxation lam`, the slope `reluSlope` unless the caller names
another. The one standard activation that needs no transcendental function, and the one carrying
a nonzero slope. -/
def Layer.relu (lam : 𝕋 → 𝕋 → 𝕋 := reluSlope) : Layer S n n :=
  Layer.activation (reluRelaxation lam)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

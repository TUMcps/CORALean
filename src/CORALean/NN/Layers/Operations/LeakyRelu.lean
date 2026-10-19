module

public import CORALean.Global.Float.FloatOps
public import CORALean.NN.Layers.Operations.Activation
public import CORALean.NN.Layers.Operations.LeakyReluRelaxation

@[expose] public section

/-!
# The leaky ReLU layer

CORA's `nnLeakyReLULayer`: `Layer.activation` at `leakyReluRelaxation α lam`, the slope
`aux_leakyReluSlope α` unless the caller names another. `α` is CORA's `alpha`, `0.01` by default.
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
open Float Float.FloatOps


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Exact on a stable neuron; the secant where the neuron crosses. -/
def aux_leakyReluSlope (α l u : 𝕋) : 𝕋 :=
  if le u zero then α else if le zero l then one else divUp (subUp u (mulDown α l)) (subDown u l)


-- =====================================  MAIN DEFINITION  ====================================== --

def Layer.leakyRelu (α : 𝕋) (lam : 𝕋 → 𝕋 → 𝕋 := aux_leakyReluSlope α) : Layer S n n :=
  Layer.activation (leakyReluRelaxation α lam)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

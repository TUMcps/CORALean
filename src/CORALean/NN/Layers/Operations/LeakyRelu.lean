module

public import CORALean.Global.Float.FloatOps
public import CORALean.NN.Layers.Operations.Activation
public import CORALean.NN.Layers.Operations.LeakyReluRelaxation
public import CORALean.Global.StepOf

@[expose] public section

/-!
# The leaky ReLU layer

CORA's `nnLeakyReLULayer`: `Layer.activation` at `leakyReluRelaxation α lam`, the slope
`step_leakyReluSlope α` unless the caller names another. `α` is CORA's `alpha`, `0.01` by default.

## Inputs
* `α` – slope below zero
* `lam` – slope choice for each box

## Output
* layer applying the leaky ReLU relaxation to every neuron
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


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- Exact on a stable neuron; the secant where the neuron crosses. -/
@[step_of Layer.leakyRelu]
def step_leakyReluSlope (α l u : 𝕋) : 𝕋 :=
  if le u zero then α else if le zero l then one else divUp (subUp u (mulDown α l)) (subDown u l)


-- =====================================  MAIN DEFINITION  ====================================== --

def Layer.leakyRelu (α : 𝕋) (lam : 𝕋 → 𝕋 → 𝕋 := step_leakyReluSlope α) : Layer S n n :=
  Layer.activation (leakyReluRelaxation α lam)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

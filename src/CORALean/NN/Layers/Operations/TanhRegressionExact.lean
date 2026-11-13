module

public import CORALean.NN.Layers.Operations.Activation
public import CORALean.NN.Layers.Operations.SigmoidRegressionExactRelaxation
public import CORALean.NN.Layers.Operations.RelaxationOfAffineConj
public import CORALean.NN.Layers.Operations.DoubleRounding
public import CORALean.Global.StepOf

@[expose] public section

/-!
# The tanh layer at the regression line, with the exact error

CORA's `nnTanhLayer` at its default `poly_method = 'regression'`, order 1: `Layer.activation` at
the sigmoid's regression relaxation with the exact error through `tanh t = 2 σ(2 t) - 1`, doubled
box and all. The
points `2 x_i` are equally spaced on the doubled box, so the least-squares line of the sigmoid
there is the least-squares line of `tanh` on the box.

## Inputs
* `k` – reduction depth of the exponential

## Output
* layer applying the relaxation to every neuron
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       13-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet ContSetLike Float.FloatOps

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋]
  {S : ℕ → Type} [∀ n, ContSetLike (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat 𝕋) S] [Float.IntervalOuter S 𝕋] [Float.OfInterval S 𝕋] {n : ℕ}


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- `sigmoidRegressionExactRelaxation` read through `tanh_eq_sigmoid`: `a = b = 2`, `c = -1`. -/
@[step_of Layer.tanhRegressionExact]
def step_tanhRegressionExactRelaxation (k : ℕ) : Relaxation 𝕋 :=
  Relaxation.ofAffineConj (sigmoidRegressionExactRelaxation k) doubleRounding doubleRounding
    (neg one)


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The tanh layer at the regression line, with the exact error. -/
def Layer.tanhRegressionExact (k : ℕ) : Layer S n n :=
  Layer.activation (step_tanhRegressionExactRelaxation k)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

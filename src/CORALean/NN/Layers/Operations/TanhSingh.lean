module

public import CORALean.NN.Layers.Operations.Activation
public import CORALean.NN.Layers.Operations.SigmoidSinghRelaxation
public import CORALean.NN.Layers.Operations.RelaxationOfAffineConj
public import CORALean.NN.Layers.Operations.DoubleRounding
public import CORALean.Global.StepOf

@[expose] public section

/-!
# The tanh layer by Singh's transformer

CORA's `nnTanhLayer` at `poly_method = 'singh'`, order 1 [1, Thm. 3.2]: `Layer.activation` at the
sigmoid's relaxation by Singh's transformer through `tanh t = 2 σ(2 t) - 1`, doubled box and all.
The slope is `4 min(σ'(2 l), σ'(2 u)) = min(tanh'(l), tanh'(u))`. `Layer.tanh` is the tighter
relaxation; this is what CORA computes.

## Inputs
* `k` – reduction depth of the exponential

## Output
* layer applying the relaxation to every neuron

## References

* [1] [G. Singh, T. Gehr, M. Mirman, M. Püschel and M. Vechev. "Fast and Effective Robustness
      Certification". Advances in Neural Information Processing Systems,
      2018.](../../../../../references/2018/singh-neurips-deepz.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       12-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet ContSetLike Float.FloatOps

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋]
  {S : ℕ → Type} [∀ n, ContSetLike (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat 𝕋) S] [Float.IntervalOuter S 𝕋] [Float.OfInterval S 𝕋] {n : ℕ}


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- `sigmoidSinghRelaxation` read through `tanh_eq_sigmoid`: `a = b = 2`, `c = -1`. -/
@[step_of Layer.tanhSingh]
def step_tanhSinghRelaxation (k : ℕ) : Relaxation 𝕋 :=
  Relaxation.ofAffineConj (sigmoidSinghRelaxation k) doubleRounding doubleRounding (neg one)


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The tanh layer at Singh's slope. -/
def Layer.tanhSingh (k : ℕ) : Layer S n n := Layer.activation (step_tanhSinghRelaxation k)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

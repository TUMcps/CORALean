module

public import CORALean.Global.Tensor
public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# The networks CORA's `nonlinearSysDT` accepts

`NeuralNetwork` holds each layer as an opaque `Enclose` kind, so nothing can tell a linear layer
from any other: the conversion CORA's `@neuralNetwork/nonlinearSysDT.m` performs reads the layer
types. This is the chain it reads, as data: the layer kinds the conversion supports
(`nnLinearLayer`, `nnElementwiseAffineLayer`, `nnTanhLayer`, `nnReLULayer`, `nnSigmoidLayer`),
first layer first, the dimensions chaining. CORA throws on any other kind, and ignores a trailing
softmax, which is a network without it.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

/-- A network of the layers CORA's `nonlinearSysDT` accepts: linear, elementwise affine, `tanh`,
`relu` and `sigmoid`. -/
inductive SmoothNetwork : ℕ → ℕ → Type where
  | output {n : ℕ} : SmoothNetwork n n
  | linear {n m k : ℕ} (W : Mat ℝ m n) (b : Vec ℝ m) (rest : SmoothNetwork m k) :
      SmoothNetwork n k
  | elementwiseAffine {n k : ℕ} (scale offset : Vec ℝ n) (rest : SmoothNetwork n k) :
      SmoothNetwork n k
  | tanh {n k : ℕ} (rest : SmoothNetwork n k) : SmoothNetwork n k
  | relu {n k : ℕ} (rest : SmoothNetwork n k) : SmoothNetwork n k
  | sigmoid {n k : ℕ} (rest : SmoothNetwork n k) : SmoothNetwork n k

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

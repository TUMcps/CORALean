module

public import CORALean.NN.Operations.SmoothNetworkEval
public import CORALean.NN.Operations.SmoothNetworkNu

@[expose] public section

/-!
# CORA's `neuralNetwork/nonlinearSysDT`: the output function

CORA builds the output function `f(x, u)` of a network by nesting the layers' expressions with one
slice of `u` added to each linear layer's bias, so that `f(x, 0)` is `evaluate(net, x)`.

CORA's elementwise-affine layer contributes `(f) + offset` and drops its scale, though its own
`evaluateNumeric` is `scale .* input + offset`; here the scale is kept, so that the stated
`f(x, 0) = evaluate(net, x)` holds. See `SmoothNetwork.elementwiseAffine_cora_counterexample`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `f(x, u)`: each linear layer adds its own block of `u` to its bias. -/
noncomputable def SmoothNetwork.outputFn :
    ∀ {n k : ℕ} (N : SmoothNetwork n k), Vec ℝ n → Vec ℝ N.nu → Vec ℝ k
  | _, _, .output, x, _ => x
  | _, _, .linear (m := m) W b rest, x, u =>
      rest.outputFn (W *ᵥ x + b + fun i => u (Fin.castAdd rest.nu i))
        fun j => u (Fin.natAdd m j)
  | _, _, .elementwiseAffine scale offset rest, x, u =>
      rest.outputFn (fun i => scale i * x i + offset i) u
  | _, _, .tanh rest, x, u => rest.outputFn (fun i => Real.tanh (x i)) u
  | _, _, .relu rest, x, u => rest.outputFn (fun i => Real.relu (x i)) u
  | _, _, .sigmoid rest, x, u => rest.outputFn (fun i => Real.sigmoid (x i)) u

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

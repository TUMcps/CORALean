import CORALean.NN.Layers.Definitions.EvaluateSinghNeuronCora

/-!
# A two-neuron network through CORA's `'singh'` neuron step

`neuralNetwork.evaluate` with `options.nn.poly_method = 'singh'` on a zonotope: the linear layer
`x ↦ (a₁ x + b₁, a₂ x + b₂)`, the activation layer `nnActLayerFromHandle(f, [], 1)` whose
neurons each run `NN.evaluateSinghNeuronCora`, and the linear layer `(z₁, z₂) ↦ z₁ + z₂`. The
two neurons share the input generator, which the second linear layer adds up, and each carries
its error as a fresh generator. The result is the interval `center ± (|generator| + |d₁| + |d₂|)`
of the output zonotope.

A single neuron cannot show a miss: for a monotone `f` the band is exact at both ends of the
interval. The shared generator is what makes the error of one neuron visible.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The output interval of the network on the input zonotope `c + g ε`. -/
noncomputable def NN.evaluateSinghCora (f df : ℝ → ℝ) (a₁ b₁ a₂ b₂ c g : ℝ) : Set ℝ :=
  let n₁ := NN.evaluateSinghNeuronCora f df (a₁ * c + b₁) (a₁ * g)
  let n₂ := NN.evaluateSinghNeuronCora f df (a₂ * c + b₂) (a₂ * g)
  {y | ∃ s e₁ e₂ : ℝ, |s| ≤ 1 ∧ |e₁| ≤ 1 ∧ |e₂| ≤ 1 ∧
    y = (n₁.1 + n₂.1) + (n₁.2.1 + n₂.2.1) * s + n₁.2.2 * e₁ + n₂.2.2 * e₂}

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

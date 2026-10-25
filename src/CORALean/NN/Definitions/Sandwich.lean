module

public import CORALean.NN.Layers.Definitions.Basic
public import CORALean.NN.Layers.Definitions.Relaxation
public import CORALean.NN.Layers.Instances
public import CORALean.NN.Layers.Operations.ActivationLayerOf
public import CORALean.NN.NeuralNetwork
public import CORALean.NN.Operations.Basic

@[expose] public section

/-!
# The sandwich a reduction replaces

Linear, activation, linear: the three layers `ReducesAt.merge` replaces by a reduced sandwich,
and the shape [1]'s neuron merging is stated on. ℝ-only, as the activation is the hypothesis
`R.IsSound σ` beside it.

## Inputs
* `n` – input width
* `n₁` – hidden width
* `n₂` – output width
* `W0` – first linear layer's weights
* `b0` – first linear layer's bias
* `σ` – activation function
* `R` – relaxation of the activation
* `W1` – second linear layer's weights
* `b1` – second linear layer's bias

## Hypotheses
* `hR` – relaxation is sound for the activation

## Output
* network of linear, activation, linear layers

## References

* [1] T. Ladner and M. Althoff. "Fully Automatic Neural Network Reduction for Formal Verification".
      Transactions on Machine Learning Research, 2025.
-/

-- Authors:       Claude Opus 5.5
-- Written:       06-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat ℝ) S] [Real.IntervalOuter S] [Real.OfInterval S]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The unreduced sandwich a `merge` step replaces: linear, activation, linear. -/
noncomputable def sandwich {n n₁ n₂ : ℕ} (W0 : Mat ℝ n₁ n) (b0 : Vec ℝ n₁) {σ : ℝ → ℝ}
    {R : Relaxation ℝ} (hR : R.IsSound σ) (W1 : Mat ℝ n₂ n₁) (b1 : Vec ℝ n₂) :
    NeuralNetwork S n n₂ :=
  .layer (LinearLayer.mk W0 b0)
    (.layer (ActivationLayer.of (n := n₁) hR) (.ofLayer (LinearLayer.mk W1 b1)))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

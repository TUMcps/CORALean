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
`R.Sound σ` beside it.

## References

* [1] T. Ladner and M. Althoff. "Fully Automatic Neural Network Reduction for
      Formal Verification". TMLR. arXiv:2305.01932.
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
    {R : Relaxation ℝ} (hR : R.Sound σ) (W1 : Mat ℝ n₂ n₁) (b1 : Vec ℝ n₂) :
    NeuralNetwork S n n₂ :=
  .layer (LinearLayer.mk W0 b0)
    (.layer (ActivationLayer.of (n := n₁) hR) (.ofLayer (LinearLayer.mk W1 b1)))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

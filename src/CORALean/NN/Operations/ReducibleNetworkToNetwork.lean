module

public import CORALean.NN.Operations.ReducedLinearToLayer
public import CORALean.NN.Layers.Instances

@[expose] public section

/-!
# The network [1, Eq. 2]'s layers form

Each pair unfolded into its two layers — `W h + b ⊕ I'`, then the activation at the proof the
pair stores — which is the network of layers every enclosure theorem reads. The
linear layer runs on `I'.nonemptyHull`, which is `I'` whenever `I'` is nonempty.

## Inputs
* none

## Output
* network of the linear layers with error boxes and the activations

## References

* [1] T. Ladner and M. Althoff. "Fully Automatic Neural Network Reduction for
      Formal Verification". TMLR. arXiv:2305.01932.
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋]
  {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat 𝕋) S] [Float.IntervalOuter S 𝕋] [Float.OfInterval S 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The layers [1, Eq. 2] names: `W h + b ⊕ I'`, then the activation. -/
def ReducibleNetwork.toNetwork : ∀ {n m : ℕ}, ReducibleNetwork 𝕋 n m → NeuralNetwork S n m
  | _, _, .nil => .output
  | _, _, .cons L R hR _ rest =>
      .layer (LinearWithErrorLayer.mk L.W L.b L.I')
        (.layer (⟨R, hR, rfl⟩ : ActivationLayer 𝕋 _ _) rest.toNetwork)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

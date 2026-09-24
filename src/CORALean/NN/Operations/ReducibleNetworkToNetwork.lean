import CORALean.NN.Operations.ReducedLinearToLayer
import CORALean.NN.Layers.Operations.Activation

/-!
# The network [1, Eq. 2]'s layers form

Each pair unfolded into its two layers — `W h + b ⊕ I'`, then the activation — which is the
network of layers every enclosure theorem reads.

## References

* [1] T. Ladner and M. Althoff. "Fully Automatic Neural Network Reduction for
      Formal Verification". TMLR. arXiv:2305.01932.
-/

-- Authors:       Tobias Ladner
-- Written:       23-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋]
  {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat 𝕋) S] [Float.IntervalOuter S 𝕋] [Float.OfInterval S 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The layers [1, Eq. 2] names: `W h + b ⊕ I'`, then the activation. -/
def ReducibleNetwork.toNetwork : ∀ {n m : ℕ}, ReducibleNetwork 𝕋 n m → NeuralNetwork S n m
  | _, _, .nil => .nil
  | _, _, .cons L R _ rest => .cons L.toLayer (.cons (Layer.activation R) rest.toNetwork)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

import CORALean.NN.Layers.Sigmoid
import CORALean.NN.Theorems.SensitivityActivation

/-!
# The sigmoid layer's sensitivity

`Layer.activation_sensitivity` at `hasDerivAt_sigmoid`, which the layer already
carries for its relaxation's derivative bracket: the same fact pays for the
enclosure and for the heuristic that decides where to tighten it.

`sigmoidDeriv` is `σ t · σ (-t)`, so the diagonal is bounded by the bracket
`Sigmoid` already proves — a neuron deep in saturation weighs almost nothing.
-/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix ContSet Plus Mtimes IntervalOuter OfInterval

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat ℝ) S] [IntervalOuter S] [OfInterval S] {n : ℕ}

theorem Layer.sigmoid_sensitivity (x : Vec ℝ n) :
    (Layer.sigmoid (S := S) (n := n)).sensitivity x
      = Matrix.diagonal fun i => sigmoidDeriv (x i) :=
  Layer.activation_sensitivity sigmoidRelaxation hasDerivAt_sigmoid x

end CORALean.Real

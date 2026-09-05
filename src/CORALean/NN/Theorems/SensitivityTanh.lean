import CORALean.NN.Layers.Tanh
import CORALean.NN.Theorems.SensitivityActivation

/-!
# The tanh layer's sensitivity

`Layer.activation_sensitivity` at `hasDerivAt_tanh`, so the diagonal is the
sigmoid's own, at twice the argument and four times the size — the affine
conjugation that carries the relaxation carries the heuristic with it.
-/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix ContSet Plus Mtimes IntervalOuter OfInterval

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat ℝ) S] [IntervalOuter S] [OfInterval S] {n : ℕ}

theorem Layer.tanh_sensitivity (x : Vec ℝ n) :
    (Layer.tanh (S := S) (n := n)).sensitivity x
      = Matrix.diagonal fun i => 4 * sigmoidDeriv (2 * x i) :=
  Layer.activation_sensitivity tanhRelaxation hasDerivAt_tanh x

end CORALean.Real

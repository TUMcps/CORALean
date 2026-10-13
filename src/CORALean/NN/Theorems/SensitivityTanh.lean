import CORALean.NN.Layers.Definitions.Sigmoid
import CORALean.NN.Layers.Definitions.TanhRelaxation
import CORALean.NN.Layers.Operations.Tanh
import CORALean.NN.Layers.Theorems.Real.HasDerivAtTanh
import CORALean.NN.Theorems.SensitivityActivation

/-!
# The tanh layer's sensitivity

`Layer.activation_sensitivity` at `hasDerivAt_tanh`, so the diagonal is the
sigmoid's own, at twice the argument and four times the size — the affine
conjugation that carries the relaxation carries the heuristic with it.
-/

-- Authors:       Claude Opus 5
-- Written:       05-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Plus Mtimes Real.IntervalOuter Real.OfInterval

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat ℝ) S] [Real.IntervalOuter S] [Real.OfInterval S] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Layer.tanh_sensitivity (x : Vec ℝ n) :
    layerSensitivity (fun (y : Vec ℝ n) i => Real.tanh (y i)) x
      = Matrix.diagonal fun i => 4 * Real.sigmoidDeriv (2 * x i) :=
  Layer.activation_sensitivity Real.hasDerivAt_tanh x

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

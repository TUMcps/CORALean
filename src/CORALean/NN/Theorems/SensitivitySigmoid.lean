import CORALean.NN.Layers.Definitions.Sigmoid
import CORALean.NN.Layers.Definitions.SigmoidRelaxation
import CORALean.NN.Layers.Operations.Sigmoid
import CORALean.NN.Layers.Theorems.Real.HasDerivAtSigmoid
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


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Plus Mtimes Real.IntervalOuter Real.OfInterval

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat ℝ) S] [Real.IntervalOuter S] [Real.OfInterval S] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Layer.sigmoid_sensitivity (x : Vec ℝ n) :
    layerSensitivity (fun (y : Vec ℝ n) i => Real.sigmoid (y i)) x
      = Matrix.diagonal fun i => Real.sigmoidDeriv (x i) :=
  Layer.activation_sensitivity Real.hasDerivAt_sigmoid x

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

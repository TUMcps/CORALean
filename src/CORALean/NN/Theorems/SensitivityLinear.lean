import CORALean.NN.Theorems.SensitivityOfMatrix
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# The linear layer's sensitivity is its weight matrix

The clean case, and the only one that does not depend on the point: `W x + b`
differs from `W x` by a constant, and a constant has no derivative to
contribute. CORA's `nnLinearLayer/evaluateSensitivity` is the same statement —
it multiplies by `W` and never looks at the stored input.

Everything that *is* a linear layer here — convolution, average pooling, batch
normalization — reads its sensitivity off this one, at its own matrix.
-/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Layer.linear_sensitivity (W : Mat ℝ m n) (b : Vec ℝ m) (x : Vec ℝ n) :
    layerSensitivity (fun y => W *ᵥ y + b) x = W :=
  Layer.sensitivity_eq_of_hasFDerivAt
    ((LinearMap.toContinuousLinearMap (Matrix.mulVecLin W)).hasFDerivAt.add_const b)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

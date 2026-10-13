module

public import CORALean.Global.Tensor
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin

@[expose] public section

/-!
# The Jacobian matrix

The matrix of the Fréchet derivative of `g : ℝⁿ → ℝᵐ` at `x`, the `∂g/∂x` of CORA's symbolic
`jacobian` files. `fderiv` is `0` where `g` is not differentiable, so a statement about this
matrix assumes differentiability where it needs it.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The Jacobian of `g` at `x`. -/
noncomputable def jacobianMat (g : Vec ℝ n → Vec ℝ m) (x : Vec ℝ n) : Mat ℝ m n :=
  LinearMap.toMatrix' (fderiv ℝ g x).toLinearMap

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

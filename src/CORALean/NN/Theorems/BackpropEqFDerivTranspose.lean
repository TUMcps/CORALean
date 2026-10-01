import CORALean.NN.Theorems.BackpropEqTranspose
import CORALean.NN.Theorems.SensitivityFDeriv

/-!
# Backpropagation is the transposed derivative wherever the layers are differentiable

`Chain.backprop_eq_transpose_mulVec` with `Chain.sensitivity_eq_fderiv`: `(D c.eval x)ᵀ g`,
the gradient of `g ⬝ c.eval`.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

theorem Chain.backprop_eq_fderiv_transpose {n m : ℕ} (c : Chain n m) (x : Vec ℝ n) (g : Vec ℝ m)
    (h : c.DifferentiableChain x) :
    c.backprop x g
      = (LinearMap.toMatrix' (fderiv ℝ c.eval x : Vec ℝ n →L[ℝ] Vec ℝ m).toLinearMap)ᵀ *ᵥ g := by
  rw [c.backprop_eq_transpose_mulVec, c.sensitivity_eq_fderiv x h]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

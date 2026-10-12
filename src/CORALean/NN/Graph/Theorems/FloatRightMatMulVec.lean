import CORALean.NN.Graph.Operations.FloatRightMat
import CORALean.Global.Float.SoundFloatArithmetic

/-!
# `rightMat` reads back as `H ↦ H W`

At the reals the stored entries denote, the matrix times the stacked node features is the stack of
`H W`: the entries are those of `W` and the exact zero, so nothing is lost.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic Matrix

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {N F₁ F₂ : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem GNN.rightMat_mulVec (W : Mat 𝕋 F₁ F₂) (H : Mat ℝ N F₁) :
    toRealMat (GNN.rightMat N W) *ᵥ GNN.flatten H = GNN.flatten (H * toRealMat W) := by
  funext r
  simp only [Matrix.mulVec, dotProduct, GNN.flatten, toRealMat, GNN.rightMat, Matrix.mul_apply]
  rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
  simp [apply_ite toReal, toReal_zero, Equiv.symm_apply_apply, mul_comm]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

import CORALean.NN.Graph.Operations.FloatLeftMat
import CORALean.Global.Float.SoundFloatArithmetic

/-!
# `leftMat` reads back as `H ↦ P H`

At the reals the stored entries denote, the matrix times the stacked node features is the stack of
`P H`: the entries are those of `P` and the exact zero, so nothing is lost.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic Matrix

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {N F : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem GNN.leftMat_mulVec (P : Mat 𝕋 N N) (H : Mat ℝ N F) :
    toRealMat (GNN.leftMat P F) *ᵥ GNN.flatten H = GNN.flatten (toRealMat P * H) := by
  funext r
  simp only [Matrix.mulVec, dotProduct, GNN.flatten, toRealMat, GNN.leftMat, Matrix.mul_apply]
  rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
  simp [apply_ite toReal, toReal_zero, Equiv.symm_apply_apply]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

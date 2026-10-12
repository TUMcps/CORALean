import CORALean.NN.Graph.Operations.FloatSumPoolMat
import CORALean.NN.Graph.Operations.SumPoolLin
import CORALean.Global.Float.SoundFloatArithmetic

/-!
# `sumPoolMat` reads back as the pooling map

The pooling matrix times the stacked node features is the exact layer's `sumPoolLin`: the entries
are the exact `1` and `0`.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic Matrix

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {N F : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem GNN.sumPoolMat_mulVec (H : Mat ℝ N F) :
    toRealMat (GNN.sumPoolMat (𝕋 := 𝕋) N F) *ᵥ GNN.flatten H
      = Real.GNN.sumPoolLin N F H := by -- --- PROOF ---
  funext j
  simp only [Matrix.mulVec, dotProduct, GNN.flatten, toRealMat, GNN.sumPoolMat]
  rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
  show _ = ∑ i, H i j
  simp [apply_ite toReal, toReal_zero, toReal_one, Equiv.symm_apply_apply]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

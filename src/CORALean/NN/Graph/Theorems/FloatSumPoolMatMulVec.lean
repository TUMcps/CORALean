module

public import CORALean.NN.Graph.Operations.FloatSumPoolMat
public import CORALean.NN.Graph.Operations.SumPoolLin
public import CORALean.Global.Float.SoundFloatArithmetic

@[expose] public section

/-!
# `sumPoolMat` reads back as the pooling map

The pooling matrix times the stacked node features is the exact layer's `sumPoolLin`: the entries
are the exact `1` and `0`.

## Inputs
* `H` – node-feature matrix

## Hypotheses
* none

## Conclusion
* the matrix applied to the stacked features is the pooled sum
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

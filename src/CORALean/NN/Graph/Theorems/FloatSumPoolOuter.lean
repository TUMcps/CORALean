module

public import CORALean.NN.Graph.Operations.FloatSumPool
public import CORALean.NN.Graph.Operations.SumPoolLin
public import CORALean.Global.Float.SoundFloatArithmetic

@[expose] public section

/-!
# The float summation pooling over-approximates the exact one

[1, Prop. 3] is an equality at the reals; at a float scalar the `mtimes` rounds, and the rounding
is in the error box, so what holds is an enclosure: every node-feature matrix `H` whose stack lies
in the input set is pooled by the exact layer into the output set.

## Inputs
* `pZ` – stacked node features
* `H` – exact node-feature matrix

## Hypotheses
* `hH` – the features lie in the set

## Conclusion
* the exact pooling of the features lies in the float pooled set

## References

* [1] [T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph Convolutional Networks
      with Uncertain Node Features and Uncertain Graph Structure". Transactions on Machine Learning
      Research, 2025.](../../../../../references/2025/ladner-tmlr-gcn.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {N F : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

section
open Matrix

/-- `aux_sumPoolMat` reads back as the pooling map. -/
private theorem GNN.aux_sumPoolMat_mulVec (H : Mat ℝ N F) : -- --- CONCL ---
    toRealMat (GNN.aux_sumPoolMat (𝕋 := 𝕋) N F) *ᵥ GNN.flatten H
      = Real.GNN.sumPoolLin N F H := by -- --- PROOF ---
  funext j
  simp only [Matrix.mulVec, dotProduct, GNN.flatten, toRealMat, GNN.aux_sumPoolMat]
  rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
  show _ = ∑ i, H i j
  simp [apply_ite toReal, toReal_zero, toReal_one, Equiv.symm_apply_apply]

end


-- =======================================  MAIN THEOREM  ======================================= --

theorem GNN.sumPool_outer (pZ : PolyZonotope (Vec 𝕋 (N * F))) (H : Mat ℝ N F)
    (hH : GNN.flatten H ∈ pZ.construct) :
    Real.GNN.sumPoolLin N F H ∈ (GNN.sumPool pZ).construct := by
  rw [← GNN.aux_sumPoolMat_mulVec (𝕋 := 𝕋)]
  exact PolyZonotope.mtimes_outer (GNN.aux_sumPoolMat N F) pZ ⟨_, hH, rfl⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

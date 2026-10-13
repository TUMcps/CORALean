import CORALean.NN.Graph.Operations.FloatSumPool
import CORALean.NN.Graph.Theorems.FloatSumPoolMatMulVec

/-!
# The float summation pooling over-approximates the exact one

[1, Prop. 3] is an equality at the reals; at a float scalar the `mtimes` rounds, and the rounding
is in the error box, so what holds is an enclosure: every node-feature matrix `H` whose stack lies
in the input set is pooled by the exact layer into the output set.

## References

* [1] T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph
      Convolutional Networks with Uncertain Node Features and Uncertain Graph
      Structure". TMLR, 2025. arXiv:2404.15065.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {N F : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem GNN.sumPool_outer (pZ : PolyZonotope (Vec 𝕋 (N * F))) (H : Mat ℝ N F)
    (hH : GNN.flatten H ∈ pZ.construct) :
    Real.GNN.sumPoolLin N F H ∈ (GNN.sumPool pZ).construct := by
  rw [← GNN.sumPoolMat_mulVec (𝕋 := 𝕋)]
  exact PolyZonotope.mtimes_outer (GNN.sumPoolMat N F) pZ ⟨_, hH, rfl⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

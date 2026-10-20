module

public import CORALean.ContSet.PolyZonotope.Real.Theorems.MapExact
public import CORALean.NN.Graph.Operations.SumPool
public import CORALean.NN.Graph.Theorems.SumPoolLinApply

@[expose] public section

/-!
# Summation pooling loses nothing

[1, Prop. 3]. `PolyZonotope.map_exact` again, here at the map that sums each feature across the
nodes. The statement is `1 H` as [1] writes it rather than the column sum the definition is, so the
guarantee can be checked against the paper without unfolding anything; `sumPoolLin_apply` carries it
across. The image lands in `Vec ℝ F`, so this equality is also the seam: a set that arrives
matrix-shaped leaves in the shape `NeuralNetwork` encloses, and nothing is lost.

## Inputs
* `pZ` – node features as a polynomial zonotope

## Hypotheses
* none

## Conclusion
* the pooled set is exactly the image of the features under summation

## References

* [1] T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph
      Convolutional Networks with Uncertain Node Features and Uncertain Graph
      Structure". TMLR, 2025. arXiv:2404.15065.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {N F : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem GNN.sumPool_exact (pZ : PolyZonotope (Mat ℝ N F)) :
    (fun H j => (GNN.onesRow N * H) 0 j) '' pZ.construct
      = (GNN.sumPool pZ).construct := by -- --- PROOF ---
  -- the paper's `1 H` read back as the linear map the propagation maps by
  have h : (fun (H : Mat ℝ N F) (j : Fin F) => (GNN.onesRow N * H) 0 j)
      = GNN.sumPoolLin N F :=
    funext fun H => funext fun j => (GNN.sumPoolLin_apply H j).symm
  rw [h]
  exact PolyZonotope.map_exact (GNN.sumPoolLin N F) pZ

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

import CORALean.ContSet.PolyZonotope.Real.Theorems.MapExact
import CORALean.NN.Graph.Pooling

/-!
# Summation pooling loses nothing

[1, Prop. 3]. `PolyZonotope.map_exact` again, here at the map that sums each
feature across the nodes.

The statement is `1 H` as [1] writes it rather than the column sum the
definition is, so that the guarantee can be checked against the paper without
unfolding anything; `sumPoolLin_apply` is what carries it across.

The image lands in `Vec ℝ F`, so this equality is also the seam: a set that
arrives matrix-shaped leaves in the shape `NeuralNetwork` encloses, and
nothing is lost crossing it.

## References

* [1] T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph
      Convolutional Networks with Uncertain Node Features and Uncertain Graph
      Structure". TMLR, 2025. arXiv:2404.15065.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


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

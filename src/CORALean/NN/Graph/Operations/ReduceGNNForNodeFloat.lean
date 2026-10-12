import Mathlib.Data.Finset.Sort
import CORALean.NN.Graph.Operations.ReduceKeepFloat
import CORALean.NN.Graph.Operations.ReducedStepsFloat
import CORALean.NN.Graph.Operations.SupportFloat

/-!
# `reduceGNNForNode`, at float
The `L`-step chain on the nodes node `v` needs, as `GNN.reduceGNNForNode`, now running: the edge
test is `GNN.support A` of the stored float adjacency matrix, the kept sets are
`GNN.reduceKeepFloat`, enumerated in increasing order by `Finset.orderEmbOfFin`, and the steps are
`GNN.reducedStepsFloat` from `X` restricted to the first set. `P` is the stored message-passing
matrix, which CORA's `updateMessagePassing` restricts and does not recompute [1, §4.3].

## References

* [1] T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph
      Convolutional Networks with Uncertain Node Features and Uncertain Graph
      Structure". TMLR, 2025. arXiv:2404.15065.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {N F : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def GNN.reduceGNNForNodeFloat (A : Mat 𝕋 N N) (v : Fin N) (L : ℕ) (P : Interval (Mat 𝕋 N N))
    (W : ℕ → Interval (Mat 𝕋 F F)) (X : Interval (Mat 𝕋 N F)) :
    Interval (Mat 𝕋 (GNN.reduceKeepFloat (GNN.support A) v L L).card F) :=
  GNN.reducedStepsFloat P L (fun k => (GNN.reduceKeepFloat (GNN.support A) v L k).card)
    (fun k => (GNN.reduceKeepFloat (GNN.support A) v L k).orderEmbOfFin rfl) W
    (X.submatrix ((GNN.reduceKeepFloat (GNN.support A) v L 0).orderEmbOfFin rfl) id)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

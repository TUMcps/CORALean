module

public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Fintype.Basic
public import CORALean.NN.Graph.Operations.ReducedStepsFloat
public import CORALean.NN.Graph.Operations.SupportFloat
public import CORALean.NN.Graph.Operations.ReduceKeepFloat
public import CORALean.NN.Graph.Operations.BallFloat

@[expose] public section

/-!
# `reduceGNNForNode`, at float
The `L`-step chain on the nodes node `v` needs, as `GNN.reduceGNNForNode`, now running: the edge
test is `GNN.support A` of the stored float adjacency matrix, the kept sets are
`GNN.reduceKeepFloat`, enumerated in increasing order by `Finset.orderEmbOfFin`, and the steps
are `GNN.reducedStepsFloat` from `X` restricted to the first set. `P` is the stored message-passing
matrix, which CORA's `updateMessagePassing` restricts and does not recompute [1, §4.3].

## Inputs
* `A` – float adjacency matrix
* `v` – node of interest
* `L` – number of message-passing steps
* `P` – interval message-passing matrix
* `W` – interval weights of the steps
* `X` – interval node-feature matrix

## Output
* interval features of the kept nodes after the reduced network

## References

* [1] T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph Convolutional Networks
      with Uncertain Node Features and Uncertain Graph Structure". Transactions on Machine Learning
      Research, 2025.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {N F : ℕ}


section
variable {N : ℕ}


end


section
variable {N : ℕ}


end


-- =====================================  MAIN DEFINITION  ====================================== --

def GNN.reduceGNNForNodeFloat (A : Mat 𝕋 N N) (v : Fin N) (L : ℕ) (P : Interval (Mat 𝕋 N N))
    (W : ℕ → Interval (Mat 𝕋 F F)) (X : Interval (Mat 𝕋 N F)) :
    Interval (Mat 𝕋 (GNN.reduceKeepFloat (GNN.support A) v L L).card F) :=
  GNN.reducedStepsFloat P L (fun k => (GNN.reduceKeepFloat (GNN.support A) v L k).card)
    (fun k => (GNN.reduceKeepFloat (GNN.support A) v L k).orderEmbOfFin rfl) W
    (X.submatrix ((GNN.reduceKeepFloat (GNN.support A) v L 0).orderEmbOfFin rfl) id)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

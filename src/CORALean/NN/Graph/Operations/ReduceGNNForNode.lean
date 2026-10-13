module

public import CORALean.NN.Graph.Operations.ReduceKeep
public import CORALean.NN.Graph.Operations.ReducedSteps

@[expose] public section

/-!
# `reduceGNNForNode`: the network on the nodes node `v` needs
The `L`-step chain of `GNN.evalSteps`, run as CORA's reduced network [1, §4.3] does: the input
restricted to the nodes within `L + 1` hops of `v`, each step on the kept nodes, the kept set
shrinking by one hop per step (`GNN.reduceKeep`) down to `{v}`. The layers between two
message-passing steps act per node, so they are the weights `W` here; the result has one row,
`v`'s, when `L ≥ 1`.

## References

* [1] T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph
      Convolutional Networks with Uncertain Node Features and Uncertain Graph
      Structure". TMLR, 2025. arXiv:2404.15065.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {N F : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The reduced network at node `v`: `GNN.reducedSteps` on the kept sets, from `X` restricted to
the first. -/
noncomputable def GNN.reduceGNNForNode (A : Mat ℝ N N) (v : Fin N) (L : ℕ)
    (W : ℕ → Mat ℝ F F) (X : Mat ℝ N F) : Matrix ↥(GNN.reduceKeep A v L L) (Fin F) ℝ :=
  GNN.reducedSteps (GNN.messagePassing A) L (GNN.reduceKeep A v L) W
    (X.submatrix (fun a : ↥(GNN.reduceKeep A v L 0) => (a : Fin N)) id)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

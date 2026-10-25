module

public import CORALean.NN.Graph.Operations.Bfs
public import CORALean.NN.Graph.Theorems.BfsVisitedEqBall
public import CORALean.NN.Graph.Theorems.EvalStepsLayersRowBallOfAdjacencyUncertain

@[expose] public section

/-!
# `[1, Sec. 4.3]`'s subgraph, found by the breadth-first search

The subgraph a caller verifies is the `(κ' + 1)`-hop neighbourhood of the node of interest that
a breadth-first search over every uncertain edge finds, `bfs (adjMax A U) v (L + 1)`. A `κ`
enumerating it carries row `v` of the layered network, at every admissible weighting of the
uncertain edges, to the same row of the network run on the subgraph with its own message passing:
`evalStepsLayers_row_ball_of_adjacency_uncertain` with the ball read off `bfs_visited`.

## Inputs
* `N` – number of nodes
* `F` – feature width
* `m` – number of uncertain edges
* `A` – adjacency matrix
* `U` – uncertain edges
* `lam` – weights of the uncertain edges
* `v` – node of interest
* `L` – number of steps
* `K` – number of kept nodes
* `κ` – indices of the kept nodes
* `g` – per-node layers
* `X` – node-feature matrix

## Hypotheses
* `hA` – adjacency entries are nonnegative
* `hSymm` – adjacency matrix is symmetric
* `hlam` – edge weights lie in the unit interval
* `hinj` – kept indices are distinct
* `hκ` – kept nodes contain the search's visited set

## Conclusion
* the node's row is computable on the subgraph the search finds

## References

* [1] T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph Convolutional Networks
      with Uncertain Node Features and Uncertain Graph Structure". Transactions on Machine Learning
      Research, 2025.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Sec. 4.3]: a node's output row of the layered network is computed on the subgraph the
breadth-first search finds, with message passing computed on that subgraph alone. -/
theorem GNN.evalStepsLayers_row_bfs_uncertain {N F m : ℕ} (A : Mat ℝ N N)
    (U : Fin m → Fin N × Fin N) (hA : ∀ i j, 0 ≤ A i j) (hSymm : ∀ i j, A i j = A j i)
    {lam : Fin m → ℝ} (hlam : ∀ e, 0 ≤ lam e ∧ lam e ≤ 1) (v : Fin N) (L : ℕ) {K : ℕ}
    (κ : Fin K → Fin N) (hinj : Function.Injective κ)
    (hκ : (GNN.bfs (GNN.adjMax A U) v (L + 1)).1 ⊆ Finset.univ.image κ)
    (g : Fin L → Vec ℝ F → Vec ℝ F) (X : Mat ℝ N F) : -- --- CONCL ---
    ∃ φ : Fin (GNN.ball (GNN.adjAt A U lam) v L).card → Fin K,
      GNN.evalStepsLayers (GNN.messagePassing (GNN.adjAt A U lam)) L g X v
        = GNN.evalStepsLayers
            ((GNN.messagePassing ((GNN.adjAt A U lam).submatrix κ κ)).submatrix φ φ) L
            g ((X.submatrix κ id).submatrix φ id)
            (GNN.ballEnumIdx (GNN.adjAt A U lam) v L) := by -- --- PROOF ---
  rw [GNN.bfs_visited] at hκ
  exact GNN.evalStepsLayers_row_ball_of_adjacency_uncertain A U hA hSymm hlam v L κ hinj hκ g X

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

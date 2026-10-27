module

public import CORALean.NN.Graph.Theorems.BallEnumBallEnumIdx
public import CORALean.NN.Graph.Theorems.BallEnumInjective
public import CORALean.NN.Graph.Theorems.EvalStepsLayersRowBall
public import CORALean.NN.Graph.Theorems.MemBallEnumIff

@[expose] public section

/-!
# `[1, Sec. 4.3]`'s locality for the layered network, with no `κ` left to build

`evalStepsLayers_row_ball` at `ballEnum`, the `κ` built once: its injectivity, its image the
ball, and `ballEnumIdx` the place of `v` in it leave no hypothesis to discharge.

## Inputs
* `N` – number of nodes
* `F` – feature width
* `A` – adjacency matrix
* `v` – node of interest
* `L` – number of steps
* `g` – per-node layers
* `X` – node-feature matrix

## Hypotheses
* none

## Conclusion
* the node's row of the full chain equals its row on the enumerated ball

## References

* [1] [T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph Convolutional Networks
      with Uncertain Node Features and Uncertain Graph Structure". Transactions on Machine Learning
      Research, 2025.](../../../../../references/2025/ladner-tmlr-gcn.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

/-- Row `v` of an `L`-step layered chain equals `ballEnumIdx`'s row of the chain run on the
subgraph the ball itself enumerates. -/
theorem GNN.evalStepsLayers_row_ball_enum {N F : ℕ} (A : Mat ℝ N N) (v : Fin N) (L : ℕ)
    (g : Fin L → Vec ℝ F → Vec ℝ F) (X : Mat ℝ N F) :
    GNN.evalStepsLayers (GNN.messagePassing A) L g X v
      = GNN.evalStepsLayers ((GNN.messagePassing A).submatrix (GNN.ballEnum A v L)
          (GNN.ballEnum A v L)) L g (X.submatrix (GNN.ballEnum A v L) id)
          (GNN.ballEnumIdx A v L) :=
  GNN.evalStepsLayers_row_ball A v L (GNN.ballEnum A v L) (GNN.ballEnum_injective A v L)
    (GNN.mem_ballEnum_iff A v L) g X (GNN.ballEnumIdx A v L) (GNN.ballEnum_ballEnumIdx A v L)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

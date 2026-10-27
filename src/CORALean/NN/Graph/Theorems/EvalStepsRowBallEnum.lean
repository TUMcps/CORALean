module

public import CORALean.NN.Graph.Theorems.BallEnumBallEnumIdx
public import CORALean.NN.Graph.Theorems.BallEnumInjective
public import CORALean.NN.Graph.Theorems.EvalStepsRowBall
public import CORALean.NN.Graph.Theorems.MemBallEnumIff

@[expose] public section

/-!
# `[1, §4.3]`'s locality, with no `κ` left to build

`evalSteps_row_ball` is correct but unusable as stated: every caller would have to construct its own
injective `κ` and prove it enumerates the ball. `ballEnum` is exactly that `κ`, built once, so this
instantiates `evalSteps_row_ball` at `ballEnum_injective`, `mem_ballEnum_iff` and
`ballEnum_ballEnumIdx` and leaves no hypothesis for the caller to discharge.

`ballEnum` is not the paper's breadth-first search, which grows outward from `v` one hop at a time;
`ball`'s own recursion filters `Finset.univ` at every radius, the same set by a worse algorithm.

## Inputs
* `N` – number of nodes
* `F` – feature width
* `A` – adjacency matrix
* `v` – node of interest
* `L` – number of steps
* `W` – weights of the steps
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

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

/-- Row `v` of an `L`-step chain equals `ballEnumIdx`'s row of the same chain run
on the subgraph the ball itself enumerates — `evalSteps_row_ball` with every
hypothesis already discharged. -/
theorem GNN.evalSteps_row_ball_enum {N F : ℕ} (A : Mat ℝ N N) (v : Fin N) (L : ℕ)
    (W : Fin L → Mat ℝ F F) (X : Mat ℝ N F) :
    GNN.evalSteps (GNN.messagePassing A) L W X v
      = GNN.evalSteps ((GNN.messagePassing A).submatrix (GNN.ballEnum A v L) (GNN.ballEnum A v L))
          L W (X.submatrix (GNN.ballEnum A v L) id) (GNN.ballEnumIdx A v L) :=
  GNN.evalSteps_row_ball A v L (GNN.ballEnum A v L) (GNN.ballEnum_injective A v L)
    (GNN.mem_ballEnum_iff A v L) W X (GNN.ballEnumIdx A v L) (GNN.ballEnum_ballEnumIdx A v L)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

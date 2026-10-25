import CORALean.NN.Graph.Theorems.EvalStepsRowBallEnum

/-!
# The `L`-ball, enumerated once, needs no `κ` from the caller

`evalSteps_row_ball_enum` at a four-node path graph: node `0`'s two-step output
already equals the same computation run on the ball's own submatrix, with no
injective `κ`, no membership characterisation of it and no index of `v` for the
caller to supply — contrast `evalSteps_row_ball`, which asks for all three.

What this does not do: `GNN.ball` still filters `Finset.univ` at every radius
rather than growing outward from `v`, so the set found here is the right one by
the wrong algorithm — `[1, §4.3]`'s breadth-first search is still unformalized.

## Inputs
* none

## Output
* adjacency matrix of the four-node path

## References

* [1] T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph Convolutional Networks
      with Uncertain Node Features and Uncertain Graph Structure". Transactions on Machine Learning
      Research, 2025.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =====================================  MAIN DEFINITION  ====================================== --

-- A four-node path graph, `0 -- 1 -- 2 -- 3`, and one scalar feature per node.

def Example.bleA : Mat ℝ 4 4 :=
  !![(0:ℝ), 1, 0, 0; 1, 0, 1, 0; 0, 1, 0, 1; 0, 0, 1, 0]

/-- The two layers' weights, `2` and `0.5`. -/
def Example.bleW : Fin 2 → Mat ℝ 1 1 := ![!![(2:ℝ)], !![(0.5:ℝ)]]

/-- The node features `1, 2, 3, 4`, one per node. -/
def Example.bleX : Mat ℝ 4 1 := !![(1:ℝ); 2; 3; 4]

/-- Node `0`'s two-step output on the path graph, restated on `ballEnum`'s own
submatrix at `ballEnumIdx` — the equality `evalSteps_row_ball_enum` gives with
no side condition left for this file to discharge. -/
example :
    GNN.evalSteps (GNN.messagePassing Example.bleA) 2 Example.bleW Example.bleX 0
      = GNN.evalSteps
          ((GNN.messagePassing Example.bleA).submatrix
            (GNN.ballEnum Example.bleA 0 2) (GNN.ballEnum Example.bleA 0 2))
          2 Example.bleW (Example.bleX.submatrix (GNN.ballEnum Example.bleA 0 2) id)
          (GNN.ballEnumIdx Example.bleA 0 2) :=
  GNN.evalSteps_row_ball_enum Example.bleA 0 2 Example.bleW Example.bleX

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

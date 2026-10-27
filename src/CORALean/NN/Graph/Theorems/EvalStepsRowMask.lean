module

public import CORALean.NN.Graph.Operations.EvalSteps
public import CORALean.NN.Graph.Operations.Mask
public import CORALean.NN.Graph.Operations.MessagePassing
public import CORALean.NN.Graph.Theorems.MemBallSelf
public import CORALean.NN.Graph.Theorems.BallMono
public import CORALean.NN.Graph.Theorems.MemBallSuccOfMessagePassing
public import CORALean.NN.Graph.Theorems.RowEqMask

@[expose] public section

/-!
# Masking outside a large enough ball changes nothing at the center

`[1, §4.3]`'s locality argument: row `v` of an `L`-step chain is the same whether or not the graph
is masked to `S`, provided `S` already contains `ball A v L` and the two starting feature matrices
agree on it. Agreeing only there, not everywhere, is not slack: the induction's recursive call sees
two genuinely different matrices and needs exactly that weaker agreement.

`GNN.row_eq_mask` is where the ball and the mask meet: at a node already in the smaller ball, every
message reaching it from outside lands in the next ball out, so masking there costs nothing.

## Inputs
* `N` – number of nodes
* `F` – feature width
* `A` – adjacency matrix
* `v` – center node
* `S` – set of nodes kept by the mask
* `L` – number of steps
* `W` – weights of the steps
* `X` – first node-feature matrix
* `Y` – second node-feature matrix

## Hypotheses
* `hS` – mask set contains the ball
* `hXY` – the two inputs agree on the ball

## Conclusion
* the center's row of the chain is the same with and without the mask

## References

* [1] [T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph Convolutional Networks
      with Uncertain Node Features and Uncertain Graph Structure". Transactions on Machine Learning
      Research, 2025.](../../../../../references/2025/ladner-tmlr-gcn.md)
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

/-- Masking outside a ball at least as large as the radius run leaves the
center's row untouched, provided the two inputs already agree on that ball. -/
theorem GNN.evalSteps_row_mask {N F : ℕ} (A : Mat ℝ N N) (v : Fin N) (S : Finset (Fin N))
    (L : ℕ) (hS : GNN.ball A v L ⊆ S) (W : Fin L → Mat ℝ F F) (X Y : Mat ℝ N F)
    (hXY : ∀ u ∈ GNN.ball A v L, X u = Y u) : -- --- CONCL ---
    GNN.evalSteps (GNN.messagePassing A) L W X v
      = GNN.evalSteps (GNN.mask S (GNN.messagePassing A)) L W Y v := by -- --- PROOF ---
  induction L generalizing X Y with
  | zero => exact hXY v (GNN.mem_ball_self A v 0)
  | succ L ih =>
      -- one step matches through `GNN.row_eq_mask`; the rest is `ih`'s shorter chain
      have hS' : GNN.ball A v L ⊆ S := (GNN.ball_subset_succ A v L).trans hS
      have hrow : ∀ u ∈ GNN.ball A v L,
          (GNN.messagePassing A * X * W 0) u = (GNN.mask S (GNN.messagePassing A) * Y * W 0) u :=
        fun u hu => by
          have h := GNN.row_eq_mask A v S L hS X Y hXY hu
          funext f
          show ∑ k, (GNN.messagePassing A * X) u k * W 0 k f
              = ∑ k, (GNN.mask S (GNN.messagePassing A) * Y) u k * W 0 k f
          exact Finset.sum_congr rfl fun k _ => by rw [congrFun h k]
      exact ih hS' (fun i => W i.succ) (GNN.messagePassing A * X * W 0)
        (GNN.mask S (GNN.messagePassing A) * Y * W 0) hrow

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

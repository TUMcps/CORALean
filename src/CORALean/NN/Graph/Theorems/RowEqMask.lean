module

public import CORALean.NN.Graph.Operations.Mask
public import CORALean.NN.Graph.Operations.MessagePassing
public import CORALean.NN.Graph.Theorems.BallSubsetSucc
public import CORALean.NN.Graph.Theorems.MemBallSuccOfMessagePassing

@[expose] public section

/-!
# Where the ball and the mask meet

`[1, §4.3]`: at a node `u` already in the smaller ball, every message reaching it from outside
lands in the next ball out by `mem_ball_succ_of_messagePassing`, so masking there costs nothing.

## Inputs
* `N` – number of nodes
* `F` – feature width
* `A` – adjacency matrix
* `v` – center node
* `S` – set of nodes kept by the mask
* `L` – radius in hops
* `X` – first node-feature matrix
* `Y` – second node-feature matrix
* `u` – node

## Hypotheses
* `hS` – mask set contains the ball one hop larger
* `hXY` – the two inputs agree on the larger ball
* `hu` – node lies in the smaller ball

## Conclusion
* the node's message row is the same with and without the mask

## References

* [1] T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph
      Convolutional Networks with Uncertain Node Features and Uncertain Graph
      Structure". TMLR, 2025. arXiv:2404.15065.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

/-- The row a step writes at a node already in the smaller ball is unaffected by
masking to `S` or by swapping `X` for `Y`, since both changes only ever touch
what lies past the larger ball. -/
theorem GNN.row_eq_mask {N F : ℕ} (A : Mat ℝ N N) (v : Fin N) (S : Finset (Fin N)) (L : ℕ)
    (hS : GNN.ball A v (L + 1) ⊆ S) (X Y : Mat ℝ N F)
    (hXY : ∀ u ∈ GNN.ball A v (L + 1), X u = Y u) {u : Fin N} (hu : u ∈ GNN.ball A v L) :
    (GNN.messagePassing A * X) u = (GNN.mask S (GNN.messagePassing A) * Y) u := by -- --- PROOF ---
  have huS : u ∈ S := hS (GNN.ball_subset_succ A v L hu)
  funext f
  simp only [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : GNN.messagePassing A u j = 0
  · simp [GNN.mask, hj]
  · have hjball : j ∈ GNN.ball A v (L + 1) := GNN.mem_ball_succ_of_messagePassing A v L hu hj
    simp [GNN.mask, huS, hS hjball, hXY j hjball]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

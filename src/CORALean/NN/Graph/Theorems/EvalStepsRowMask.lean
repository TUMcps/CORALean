import CORALean.NN.Graph.GcnSteps
import CORALean.NN.Graph.Mask
import CORALean.NN.Graph.Theorems.MemBallSelf
import CORALean.NN.Graph.Theorems.BallMono
import CORALean.NN.Graph.Theorems.MemBallSuccOfMessagePassing

/-!
# Masking outside a large enough ball changes nothing at the centre

`[1, §4.3]`'s locality argument, stated at last: row `v` of an `L`-step chain
is the same whether or not the graph is masked to `S`, provided `S` already
contains `ball A v L` and the two starting feature matrices agree on it. The
two inputs agreeing only there, not everywhere, is not slack — the induction's
recursive call sees `P * X * W 0` against `mask S P * Y * W 0`, two genuinely
different matrices, and needs exactly that weaker agreement to close.

`aux_row_eq` is where the ball and the mask meet: at a node `u` already in the
smaller ball, every message reaching it from outside lands in the next ball
out by `mem_ball_succ_of_messagePassing`, so masking there costs nothing.

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


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The row a step writes at a node already in the smaller ball is unaffected by
masking to `S` or by swapping `X` for `Y`, since both changes only ever touch
what lies past the larger ball. -/
theorem aux_row_eq {N F : ℕ} (A : Mat ℝ N N) (v : Fin N) (S : Finset (Fin N)) (L : ℕ)
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


-- =======================================  MAIN THEOREM  ======================================= --

/-- Masking outside a ball at least as large as the radius run leaves the
centre's row untouched, provided the two inputs already agree on that ball. -/
theorem GNN.evalSteps_row_mask {N F : ℕ} (A : Mat ℝ N N) (v : Fin N) (S : Finset (Fin N))
    (L : ℕ) (hS : GNN.ball A v L ⊆ S) (W : Fin L → Mat ℝ F F) (X Y : Mat ℝ N F)
    (hXY : ∀ u ∈ GNN.ball A v L, X u = Y u) :
    GNN.evalSteps (GNN.messagePassing A) L W X v
      = GNN.evalSteps (GNN.mask S (GNN.messagePassing A)) L W Y v := by -- --- PROOF ---
  induction L generalizing X Y with
  | zero => exact hXY v (GNN.mem_ball_self A v 0)
  | succ L ih =>
      -- one step matches through `aux_row_eq`; the rest is `ih`'s shorter chain
      have hS' : GNN.ball A v L ⊆ S := (GNN.ball_subset_succ A v L).trans hS
      have hrow : ∀ u ∈ GNN.ball A v L,
          (GNN.messagePassing A * X * W 0) u = (GNN.mask S (GNN.messagePassing A) * Y * W 0) u :=
        fun u hu => by
          have h := aux_row_eq A v S L hS X Y hXY hu
          funext f
          show ∑ k, (GNN.messagePassing A * X) u k * W 0 k f
              = ∑ k, (GNN.mask S (GNN.messagePassing A) * Y) u k * W 0 k f
          exact Finset.sum_congr rfl fun k _ => by rw [congrFun h k]
      exact ih hS' (fun i => W i.succ) (GNN.messagePassing A * X * W 0)
        (GNN.mask S (GNN.messagePassing A) * Y * W 0) hrow

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

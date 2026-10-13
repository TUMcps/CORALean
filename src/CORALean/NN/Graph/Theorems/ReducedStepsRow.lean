module

public import CORALean.NN.Graph.Operations.EvalSteps
public import CORALean.NN.Graph.Operations.ReducedSteps
public import CORALean.NN.Graph.Theorems.BallSubsetSucc
public import CORALean.NN.Graph.Theorems.MemBallSelf
public import CORALean.NN.Graph.Theorems.MemBallSuccOfMessagePassing

@[expose] public section

/-!
# Dropping nodes the receptive field does not reach changes nothing at `v`
Row `v` of `L` message-passing steps is the same whether the steps run on the whole graph or on
node sets `S k` that still contain `ball A v (L - k)` before step `k` [1, §4.3], the features
agreeing with `X` on `S 0`. Exact, an equality: a node outside the ball feeds no entry that a
later row inside the ball reads. The kept sets need not be nested here, only large enough.

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


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- One step at a row inside the ball: the restricted product reads the same entries as the
full one, every nonzero `P` entry of such a row landing in `S` and in the next ball out. -/
theorem aux_reducedSteps_row_step {N F : ℕ} (A : Mat ℝ N N) (v : Fin N) (r : ℕ)
    (T S : Finset (Fin N)) (hS : GNN.ball A v (r + 1) ⊆ S) (X : Mat ℝ N F)
    (Y : Matrix ↥S (Fin F) ℝ) (hY : ∀ a : ↥S, (a : Fin N) ∈ GNN.ball A v (r + 1) →
      Y a = X a) (b : ↥T) (hb : (b : Fin N) ∈ GNN.ball A v r) :
    ((GNN.messagePassing A).submatrix (fun a : ↥T => (a : Fin N)) (fun c : ↥S => (c : Fin N))
      * Y) b = (GNN.messagePassing A * X) b := by -- --- PROOF ---
  funext g
  simp only [Matrix.mul_apply, Matrix.submatrix_apply]
  -- the full sum only needs the nodes of `S`, outside it the weight is zero
  have hcut : ∑ j, GNN.messagePassing A b j * X j g
      = ∑ j ∈ S, GNN.messagePassing A b j * X j g := by
    refine (Finset.sum_subset (Finset.subset_univ _) fun j _ hj => ?_).symm
    by_contra hne
    exact hj (hS (GNN.mem_ball_succ_of_messagePassing A v r hb
      (fun h => hne (by rw [h, zero_mul]))))
  rw [hcut, ← Finset.sum_coe_sort S]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases h0 : GNN.messagePassing A b a = 0
  · simp [h0]
  · rw [hY a (GNN.mem_ball_succ_of_messagePassing A v r hb h0)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Row `v` of the reduced chain is row `v` of the full one when each kept set holds the ball
the remaining steps still read. -/
theorem GNN.reducedSteps_row {N F : ℕ} (A : Mat ℝ N N) (v : Fin N) (L : ℕ)
    (S : ℕ → Finset (Fin N)) (hS : ∀ k ≤ L, GNN.ball A v (L - k) ⊆ S k)
    (W : ℕ → Mat ℝ F F) (X : Mat ℝ N F) (Y : Matrix ↥(S 0) (Fin F) ℝ)
    (hY : ∀ a : ↥(S 0), (a : Fin N) ∈ GNN.ball A v L → Y a = X a) (a : ↥(S L))
    (ha : (a : Fin N) = v) :
    GNN.reducedSteps (GNN.messagePassing A) L S W Y a
      = GNN.evalSteps (GNN.messagePassing A) L (fun i : Fin L => W i) X v := by -- --- PROOF ---
  induction L generalizing S W X Y with
  | zero => exact ha ▸ hY a (ha ▸ GNN.mem_ball_self A v 0)
  | succ L ih =>
      -- the first step agrees on the next ball down, which is `ih`'s hypothesis
      have hrow : ∀ b : ↥(S 1), (b : Fin N) ∈ GNN.ball A v L →
          ((GNN.messagePassing A).submatrix (fun a : ↥(S 1) => (a : Fin N))
            (fun c : ↥(S 0) => (c : Fin N)) * Y * W 0) b
          = (GNN.messagePassing A * X * W 0) b := by
        intro b hb
        have h := aux_reducedSteps_row_step A v L (S 1) (S 0) (hS 0 (Nat.zero_le _)) X Y hY b hb
        funext f
        simp only [Matrix.mul_apply (M := _ * Y)]
        exact Finset.sum_congr rfl fun k _ => by rw [congrFun h k]
      exact ih (fun k => S (k + 1)) (fun k hk => by simpa using hS (k + 1) (by omega))
        (fun k => W (k + 1)) (GNN.messagePassing A * X * W 0) _
        (fun b hb => by simpa using hrow b hb) a ha
end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

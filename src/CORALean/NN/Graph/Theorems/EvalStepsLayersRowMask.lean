module

public import CORALean.NN.Graph.Operations.EvalStepsLayers
public import CORALean.NN.Graph.Theorems.MemBallSelf
public import CORALean.NN.Graph.Theorems.BallMono
public import CORALean.NN.Graph.Theorems.RowEqMask

@[expose] public section

/-!
# Masking outside a large enough ball changes nothing at the center, with a layer per step

`[1, Sec. 4.3]` for the network with its activations: row `v` of `L` message-passing steps with a
per-node layer after each is the same whether or not the graph is masked to `S`, provided `S`
contains `ball A v L` and the two starting features agree on it. A layer acts on a row alone, so
the rows that agree before it agree after it, and `evalSteps_row_mask`'s induction goes through.

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

/-- Masking outside a ball at least as large as the radius run leaves the center's row of the
layered chain untouched, provided the two inputs agree on that ball. -/
theorem GNN.evalStepsLayers_row_mask {N F : ℕ} (A : Mat ℝ N N) (v : Fin N) (S : Finset (Fin N))
    (L : ℕ) (hS : GNN.ball A v L ⊆ S) (g : Fin L → Vec ℝ F → Vec ℝ F) (X Y : Mat ℝ N F)
    (hXY : ∀ u ∈ GNN.ball A v L, X u = Y u) : -- --- STMT ---
    GNN.evalStepsLayers (GNN.messagePassing A) L g X v
      = GNN.evalStepsLayers (GNN.mask S (GNN.messagePassing A)) L g Y v := by -- --- PROOF ---
  induction L generalizing X Y with
  | zero => exact hXY v (GNN.mem_ball_self A v 0)
  | succ L ih =>
      have hS' : GNN.ball A v L ⊆ S := (GNN.ball_subset_succ A v L).trans hS
      -- one step agrees on the smaller ball, where the layer sees equal rows
      have hrow : ∀ u ∈ GNN.ball A v L,
          (Matrix.of fun u => g 0 ((GNN.messagePassing A * X) u)) u
            = (Matrix.of fun u => g 0 ((GNN.mask S (GNN.messagePassing A) * Y) u)) u :=
        fun u hu => by
          show g 0 ((GNN.messagePassing A * X) u)
            = g 0 ((GNN.mask S (GNN.messagePassing A) * Y) u)
          rw [GNN.row_eq_mask A v S L hS X Y hXY hu]
      exact ih hS' (fun i => g i.succ) _ _ hrow

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

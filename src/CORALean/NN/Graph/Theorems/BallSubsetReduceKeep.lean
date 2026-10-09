import CORALean.NN.Graph.Operations.ReduceKeep
import CORALean.NN.Graph.Theorems.BallMono

/-!
# The kept sets contain what the remaining steps read
`reduceKeep` before step `k` holds `ball A v (L - k)`, the receptive field of the `L - k`
steps still to run, for every `k ≤ L` [1, §4.3]: the margin hop is slack, and the last set `{v}`
is the ball of radius `0`.

## References

* [1] T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph
      Convolutional Networks with Uncertain Node Features and Uncertain Graph
      Structure". TMLR, 2025. arXiv:2404.15065.
-/

-- Authors:       Tobias Ladner
-- Written:       09-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

/-- The kept set before step `k` contains the ball of the steps that remain. -/
theorem GNN.ball_subset_reduceKeep {N : ℕ} (A : Mat ℝ N N) (v : Fin N) (L k : ℕ) (hk : k ≤ L) :
    GNN.ball A v (L - k) ⊆ GNN.reduceKeep A v L k := by -- --- PROOF ---
  unfold GNN.reduceKeep
  split_ifs with h
  · obtain ⟨_, rfl⟩ := h
    simp [GNN.ball]
  · exact GNN.ball_subset_succ A v (L - k)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

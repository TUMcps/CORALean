module

public import CORALean.NN.Graph.Theorems.BallSubsetBallFloat
public import CORALean.NN.Graph.Theorems.BallFloatSubsetSucc
public import CORALean.NN.Graph.Operations.ReduceKeepFloat

@[expose] public section

/-!
# The float kept set contains the ball of the steps that remain
For an edge test covering the support of `A`, the set kept before step `k` of `L` by
`GNN.reduceKeepFloat` contains the real ball `GNN.ball A v (L - k)` [1, §4.3].

## References

* [1] T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph
      Convolutional Networks with Uncertain Node Features and Uncertain Graph
      Structure". TMLR, 2025. arXiv:2404.15065.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      19-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {N : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem GNN.ball_subset_reduceKeepFloat (A : Mat ℝ N N) (E : Fin N → Fin N → Bool)
    (hE : ∀ i j, A i j ≠ 0 → E i j = true) (v : Fin N) (L k : ℕ) (hk : k ≤ L) :
    Real.GNN.ball A v (L - k) ⊆ GNN.reduceKeepFloat E v L k := by -- --- PROOF ---
  unfold GNN.reduceKeepFloat
  split_ifs with h
  · obtain ⟨_, rfl⟩ := h
    simp [Real.GNN.ball]
  · exact (GNN.ball_subset_ballFloat A E hE v (L - k)).trans
      (GNN.ballFloat_subset_succ E v (L - k))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

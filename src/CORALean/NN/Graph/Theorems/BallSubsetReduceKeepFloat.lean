module

public import CORALean.NN.Graph.Operations.Ball
public import CORALean.NN.Graph.Operations.BallFloat
public import CORALean.NN.Graph.Operations.ReduceKeepFloat

@[expose] public section

/-!
# The float kept set contains the ball of the steps that remain
For an edge test covering the support of `A`, the set kept before step `k` of `L` by
`GNN.reduceKeepFloat` contains the real ball `GNN.ball A v (L - k)` [1, §4.3].

## Inputs
* `A` – adjacency matrix
* `E` – Boolean edge test
* `v` – node of interest
* `L` – number of message-passing steps
* `k` – step index

## Hypotheses
* `hE` – the test holds wherever A is nonzero
* `hk` – step index within the number of steps

## Conclusion
* the float kept set before step k contains the real ball of the remaining steps

## References

* [1] [T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph Convolutional Networks
      with Uncertain Node Features and Uncertain Graph Structure". Transactions on Machine Learning
      Research, 2025.](../../../../../references/2025/ladner-tmlr-gcn.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      19-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {N : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

private theorem GNN.aux_ball_subset_ballFloat (A : Mat ℝ N N) (E : Fin N → Fin N → Bool)
    (hE : ∀ i j, A i j ≠ 0 → E i j = true) (v : Fin N) (r : ℕ) : -- --- CONCL ---
    Real.GNN.ball A v r ⊆ GNN.ballFloat E v r := by -- --- PROOF ---
  induction r with
  | zero => exact subset_refl _
  | succ r ih =>
      intro j hj
      obtain ⟨_, i, hi, hij⟩ := Finset.mem_filter.mp hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, i, ih hi, hij.imp id (hE i j)⟩


private theorem GNN.aux_ballFloat_subset_succ (E : Fin N → Fin N → Bool) (v : Fin N) (r : ℕ) :
    GNN.ballFloat E v r ⊆ GNN.ballFloat E v (r + 1) := by
  intro j hj
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, j, hj, Or.inl rfl⟩


-- =======================================  MAIN THEOREM  ======================================= --

theorem GNN.ball_subset_reduceKeepFloat (A : Mat ℝ N N) (E : Fin N → Fin N → Bool)
    (hE : ∀ i j, A i j ≠ 0 → E i j = true) (v : Fin N) (L k : ℕ) (hk : k ≤ L) : -- --- CONCL ---
    Real.GNN.ball A v (L - k) ⊆ GNN.reduceKeepFloat E v L k := by -- --- PROOF ---
  unfold GNN.reduceKeepFloat
  split_ifs with h
  · obtain ⟨_, rfl⟩ := h
    simp [Real.GNN.ball]
  · exact (GNN.aux_ball_subset_ballFloat A E hE v (L - k)).trans
      (GNN.aux_ballFloat_subset_succ E v (L - k))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

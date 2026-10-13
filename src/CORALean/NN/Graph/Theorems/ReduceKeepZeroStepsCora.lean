import CORALean.NN.Graph.Operations.ReduceKeep

/-!
# CORA's `reduceGNNForNode` at no message-passing step keeps the neighbours
At `numMPsteps == 0` CORA means to return the network (`% no gnn, return`) but its code has no
`return`, so it builds a reduced network whose first projection keeps the nodes within distance
`1` of `n0` and no later projection narrows that to `n0`. On the graph with one edge the kept
set of node `0` contains node `1`, though a network without message passing needs `{0}` only.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

/-- With no step, CORA's kept set at the end of a one-edge graph is not `{v}`. -/
theorem GNN.reduceKeep_zero_steps_ne_singleton :
    GNN.reduceKeep (!![0, 1; 1, 0] : Mat ℝ 2 2) 0 0 0 ≠ {0} := by -- --- PROOF ---
  intro h
  have h1 : (1 : Fin 2) ∈ GNN.reduceKeep (!![0, 1; 1, 0] : Mat ℝ 2 2) 0 0 0 := by
    simp only [GNN.reduceKeep, lt_irrefl, false_and, if_false, Nat.sub_zero, zero_add]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, 0, by simp [GNN.ball], Or.inr (by simp)⟩
  rw [h] at h1
  exact absurd (Finset.mem_singleton.mp h1) (by decide)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

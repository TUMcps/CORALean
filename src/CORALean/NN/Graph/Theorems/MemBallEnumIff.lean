module

public import CORALean.NN.Graph.Operations.BallEnum

@[expose] public section

/-!
# The enumeration's image is exactly the ball

`∃ k, ballEnum A v L k = i` is `i ∈ Set.range (ballEnum A v L)` unfolded, and
`Finset.range_orderEmbOfFin` says that range is the ball itself, coerced to a
`Set`. `Finset.mem_coe` drops the coercion back to plain membership.

## Inputs
* `N` – number of nodes
* `A` – adjacency matrix
* `v` – center node
* `L` – radius in hops
* `i` – node

## Hypotheses
* none

## Conclusion
* the node is enumerated iff it lies in the ball
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

/-- A node is hit by the enumeration exactly when it lies in the ball. -/
theorem GNN.mem_ballEnum_iff {N : ℕ} (A : Mat ℝ N N) (v : Fin N) (L : ℕ) (i : Fin N) :
    (∃ k, GNN.ballEnum A v L k = i) ↔ i ∈ GNN.ball A v L := by
  unfold GNN.ballEnum
  rw [← Set.mem_range, Finset.range_orderEmbOfFin, Finset.mem_coe]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

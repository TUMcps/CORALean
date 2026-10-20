module

public import CORALean.NN.Graph.Operations.Ball

@[expose] public section

/-!
# The ball only grows

Immediate from the `i = j` disjunct in `ball`'s successor case: every node
already in the ball reaches itself, so it stays in at the next radius too.

## Inputs
* `N` – number of nodes
* `A` – adjacency matrix
* `v` – center node
* `r` – radius in hops

## Hypotheses
* none

## Conclusion
* the ball at radius r is contained in the ball at r + 1
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

/-- One more hop never drops a node the ball already had. -/
theorem GNN.ball_subset_succ {N : ℕ} (A : Mat ℝ N N) (v : Fin N) (r : ℕ) :
    GNN.ball A v r ⊆ GNN.ball A v (r + 1) := by
  intro i hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, i, hi, Or.inl rfl⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.NN.Graph.Operations.Ball
public import CORALean.NN.Graph.Theorems.MessagePassingNeZero

@[expose] public section

/-!
# The lemma the locality proof actually runs on

Composes the ball's successor case with `messagePassing_ne_zero`: a nonzero
message out of a node already in the ball places its target one radius
further out. Everything downstream about masking reads only through this.

## Inputs
* `N` – number of nodes
* `A` – adjacency matrix
* `v` – center node
* `r` – radius in hops
* `i` – sending node
* `j` – receiving node

## Hypotheses
* `hi` – sender lies in the ball of radius r
* `hj` – message from i to j is nonzero

## Conclusion
* the receiver lies in the ball of radius r + 1
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

/-- A message reaching `j` out of a node already in the ball puts `j` in the
ball one radius further out. -/
theorem GNN.mem_ball_succ_of_messagePassing {N : ℕ} (A : Mat ℝ N N) (v : Fin N) (r : ℕ)
    {i j : Fin N} (hi : i ∈ GNN.ball A v r) (hj : GNN.messagePassing A i j ≠ 0) :
    j ∈ GNN.ball A v (r + 1) :=
  Finset.mem_filter.mpr ⟨Finset.mem_univ j, i, hi, GNN.messagePassing_ne_zero A i j hj⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

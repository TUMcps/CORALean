import CORALean.NN.Graph.Operations.Ball
import CORALean.NN.Graph.Theorems.MessagePassingNeZero

/-!
# The lemma the locality proof actually runs on

Composes the ball's successor case with `messagePassing_ne_zero`: a nonzero
message out of a node already in the ball places its target one radius
further out. Everything downstream about masking reads only through this.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


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

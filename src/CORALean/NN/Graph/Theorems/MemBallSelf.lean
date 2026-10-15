module

public import CORALean.NN.Graph.Operations.Ball

@[expose] public section

/-!
# A node is its own center

Induction on the radius: at `0` the ball is `{v}` outright, and at a successor
the `i = j` disjunct lets the base case step through unchanged, `v` reaching
itself by staying put.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

/-- `v` lies in its own ball, at every radius. -/
theorem GNN.mem_ball_self {N : ℕ} (A : Mat ℝ N N) (v : Fin N) (r : ℕ) :
    v ∈ GNN.ball A v r := by
  induction r with
  | zero => simp [GNN.ball]
  | succ r ih => exact Finset.mem_filter.mpr ⟨Finset.mem_univ v, v, ih, Or.inl rfl⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

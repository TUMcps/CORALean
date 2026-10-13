module

public import CORALean.NN.Graph.Theorems.BallSubsetSucc

@[expose] public section

/-!
# The ball is monotone in the radius

Induction on `r ≤ r'`, read as `Nat.le`'s own constructors: `refl` is
reflexivity, and `step` chains one more hop through `ball_subset_succ`.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

/-- A larger radius only ever enlarges the ball. -/
theorem GNN.ball_mono {N : ℕ} (A : Mat ℝ N N) (v : Fin N) {r r' : ℕ} (h : r ≤ r') :
    GNN.ball A v r ⊆ GNN.ball A v r' := by
  induction h with
  | refl => exact subset_refl _
  | step _ ih => exact ih.trans (GNN.ball_subset_succ A v _)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

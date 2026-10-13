module

public import CORALean.NN.Graph.Operations.Ball

@[expose] public section

/-!
# One stable step means stable forever

`ball A v (r + 1)` depends on the previous radius only through the *set*
`ball A v r`, never through `r` itself — so once two radii carry equal sets,
every later successor radius does too. `aux_ball_succ_congr` reads that
determinism off `ball`'s own recursive equation; the induction on `s` chains
it against the one hypothesised stable step.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {N : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `ball`'s successor case reads the previous radius only through its set, so
equal sets at radii `k`, `k'` give equal balls at `k + 1`, `k' + 1`. -/
theorem aux_ball_succ_congr (A : Mat ℝ N N) (v : Fin N) {k k' : ℕ}
    (h : GNN.ball A v k = GNN.ball A v k') :
    GNN.ball A v (k + 1) = GNN.ball A v (k' + 1) := by
  simp only [GNN.ball, h]


-- =======================================  MAIN THEOREM  ======================================= --

/-- One radius where the ball stops growing is every later radius too. -/
theorem GNN.ball_eq_of_succ_eq (A : Mat ℝ N N) (v : Fin N) {r : ℕ}
    (h : GNN.ball A v (r + 1) = GNN.ball A v r) (s : ℕ) :
    GNN.ball A v (r + s) = GNN.ball A v r := by
  induction s with
  | zero => rfl
  | succ s ih => exact (aux_ball_succ_congr A v ih).trans h

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

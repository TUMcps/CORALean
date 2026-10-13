module

public import CORALean.NN.Graph.Theorems.BallEnumIdx

@[expose] public section

/-!
# The enumeration really does give `v` back at its own index

`ballEnumIdx` is `Exists.choose` of exactly the witness this theorem states;
`Exists.choose_spec` is its proof.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

/-- `ballEnum` maps `v`'s own index back to `v`. -/
theorem GNN.ballEnum_ballEnumIdx {N : ℕ} (A : Mat ℝ N N) (v : Fin N) (L : ℕ) :
    GNN.ballEnum A v L (GNN.ballEnumIdx A v L) = v :=
  ((GNN.mem_ballEnum_iff A v L v).mpr (GNN.mem_ball_self A v L)).choose_spec

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

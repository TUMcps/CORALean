module

public import CORALean.NN.Graph.Theorems.MemBallEnumIff
public import CORALean.NN.Graph.Theorems.MemBallSelf

@[expose] public section

/-!
# `v`'s own index in the enumeration

`mem_ball_self` puts `v` in the ball, and `mem_ballEnum_iff` turns that into an
existential over indices — `Exists.choose` picks one.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The index `ballEnum` gives back `v` at. -/
noncomputable def GNN.ballEnumIdx {N : ℕ} (A : Mat ℝ N N) (v : Fin N) (L : ℕ) :
    Fin (GNN.ball A v L).card :=
  ((GNN.mem_ballEnum_iff A v L v).mpr (GNN.mem_ball_self A v L)).choose

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

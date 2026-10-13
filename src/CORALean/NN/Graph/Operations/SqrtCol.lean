module

public import CORALean.NN.Graph.Operations.SqrtBroadcast

@[expose] public section

/-!
# `s_j` broadcast along each column

The right factor of the normalisation `D̃^(-1/2) Ã D̃^(-1/2)`: `sqrtBroadcast`
indexed by its own column.
-/

-- Authors:       Claude Sonnet 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {N m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `s_j` broadcast along each column, the right factor of the normalisation. -/
noncomputable def GNN.sqrtCol (R : Relaxation ℝ) (A : Mat ℝ N N)
    (U : Fin m → Fin N × Fin N) : PolyZonotope (Mat ℝ N N) :=
  GNN.sqrtBroadcast R A U fun _ j => j

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

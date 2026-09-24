import CORALean.NN.Graph.Operations.SqrtBroadcast

/-!
# `s_i` broadcast along each row

The left factor of the normalisation `D̃^(-1/2) Ã D̃^(-1/2)`: `sqrtBroadcast`
indexed by its own row.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {N m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `s_i` broadcast along each row, the left factor of the normalisation. -/
noncomputable def GNN.sqrtRow (R : Relaxation ℝ) (A : Mat ℝ N N)
    (U : Fin m → Fin N × Fin N) : PolyZonotope (Mat ℝ N N) :=
  GNN.sqrtBroadcast R A U fun i _ => i

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

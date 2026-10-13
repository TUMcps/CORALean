import CORALean.NN.Graph.Operations.EdgeMat

/-!
# An uncertain edge is never negative

An edge only ever adds to a degree, which is what bounds an uncertain one.
-/

-- Authors:       Claude Sonnet 5
-- Written:       06-September-2026
-- Last update:   06-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {N : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- An edge only ever adds to a degree, which is what bounds an uncertain one. -/
theorem GNN.edgeMat_nonneg (ij : Fin N × Fin N) (a b : Fin N) : 0 ≤ GNN.edgeMat ij a b := by
  simp only [GNN.edgeMat]
  split_ifs
  exacts [zero_le_one, le_refl 0]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

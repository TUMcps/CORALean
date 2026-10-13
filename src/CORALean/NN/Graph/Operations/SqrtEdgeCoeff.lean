import CORALean.NN.Graph.Operations.DegreeCoeff
import CORALean.NN.Graph.Operations.SqrtSlope

/-!
# The generator `s_j` puts on one uncertain edge's factor

Half that edge's column sum, through the relaxation's slope: the coefficient
`sqrt_affine` reads `s_j`'s dependence on edge `e`'s factor off.
-/

-- Authors:       Claude Sonnet 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {N m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The generator `s_j` puts on edge `e`'s factor: half that edge's column sum,
through the relaxation's slope. -/
noncomputable def GNN.sqrtEdgeCoeff (R : Relaxation ℝ) (A : Mat ℝ N N)
    (U : Fin m → Fin N × Fin N) (j : Fin N) (e : Fin m) : ℝ :=
  GNN.sqrtSlope R A U j * GNN.degreeCoeff U e j / 2

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.NN.Graph.Operations.Degree
public import CORALean.NN.Graph.Operations.DegreeCoeff
public import CORALean.NN.Graph.Operations.SqrtOffset
public import CORALean.NN.Graph.Operations.SqrtSlope

@[expose] public section

/-!
# `s_j` at every uncertain edge factor zero

`s_j` at all edge factors zero, which is every edge at half weight: the
constant term of `s_j`'s affine form in the edge factors.
-/

-- Authors:       Claude Sonnet 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {N m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `s_j` at all edge factors zero, which is every edge at half weight. -/
noncomputable def GNN.sqrtConst (R : Relaxation ℝ) (A : Mat ℝ N N)
    (U : Fin m → Fin N × Fin N) (j : Fin N) : ℝ :=
  GNN.sqrtSlope R A U j * (GNN.degree A j + ∑ e, GNN.degreeCoeff U e j / 2)
    + GNN.sqrtOffset R A U j

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

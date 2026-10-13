module

public import CORALean.NN.Graph.Operations.EdgeMat

@[expose] public section

/-!
# What one uncertain edge, at full weight, adds to a degree

`degreeCoeff U e j` is edge `e`'s own column sum at `j`: the coefficient the
inverse-square-root relaxation's slope multiplies to read one edge's factor
into `s_j`.
-/

-- Authors:       Claude Sonnet 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {N m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What one uncertain edge adds to node `j`'s degree at weight `1`. -/
def GNN.degreeCoeff (U : Fin m → Fin N × Fin N) (e : Fin m) (j : Fin N) : ℝ :=
  ∑ i, GNN.edgeMat (U e) i j

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

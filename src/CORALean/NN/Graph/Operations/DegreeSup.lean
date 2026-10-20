module

public import CORALean.NN.Graph.Operations.Degree
public import CORALean.NN.Graph.Operations.EdgeDegree

@[expose] public section

/-!
# The degree of an uncertain graph, every uncertain edge switched on

The upper end of `degreeAt`'s range, read as a pair with `degree` by
`Theorems/UncertainDegreeBounds.lean`.

## Inputs
* `A` – adjacency matrix
* `U` – uncertain edges
* `j` – node

## Output
* degree of the node with every uncertain edge switched on
-/

-- Authors:       Claude Sonnet 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {N m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The degree at `j` with every uncertain edge switched on. -/
def GNN.degreeSup (A : Mat ℝ N N) (U : Fin m → Fin N × Fin N) (j : Fin N) : ℝ :=
  GNN.degree A j + GNN.edgeDegree U j

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

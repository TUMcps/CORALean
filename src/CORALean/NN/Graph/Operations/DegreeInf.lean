import CORALean.NN.Graph.Operations.Degree

/-!
# The degree of an uncertain graph, every uncertain edge switched off

`degreeInf` takes the uncertain edges and does not read them, which is what
its unused argument says: the lower end of `degreeAt`'s range, read as a pair
with `degreeSup` by `Theorems/UncertainDegreeBounds.lean`.
-/

-- Authors:       Claude Sonnet 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {N m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The degree at `j` with every uncertain edge switched off. -/
def GNN.degreeInf (A : Mat ℝ N N) (_U : Fin m → Fin N × Fin N) (j : Fin N) : ℝ :=
  GNN.degree A j

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

import CORALean.NN.Graph.Operations.EdgeMat

/-!
# What the uncertain edges add to a node's degree

`edgeMat`'s column sum across every uncertain edge, at all weights `1` — the
most an uncertain degree can gain over its fixed adjacency's own.
-/

-- Authors:       Claude Sonnet 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {N m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What the uncertain edges at `j` can add: `edgeMat`'s column sum. -/
def GNN.edgeDegree (U : Fin m → Fin N × Fin N) (j : Fin N) : ℝ :=
  ∑ e, ∑ i, GNN.edgeMat (U e) i j

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

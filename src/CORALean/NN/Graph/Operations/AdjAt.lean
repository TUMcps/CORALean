import CORALean.NN.Graph.Operations.EdgeMat

/-!
# The adjacency at one choice of uncertain edge weights

[1]'s `A(λ)`: the fixed edges of `A` plus each uncertain edge's own weighted
contribution.

## References

* [1] T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph
      Convolutional Networks with Uncertain Node Features and Uncertain Graph
      Structure". TMLR, 2025. arXiv:2404.15065.
-/

-- Authors:       Claude Sonnet 5
-- Written:       06-September-2026
-- Last update:   06-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {N m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The adjacency at one choice of edge weights, which is [1]'s `A(λ)`. -/
def GNN.adjAt (A : Mat ℝ N N) (U : Fin m → Fin N × Fin N) (lam : Fin m → ℝ) : Mat ℝ N N :=
  A + ∑ e, lam e • GNN.edgeMat (U e)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

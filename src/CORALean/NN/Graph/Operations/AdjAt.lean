module

public import CORALean.NN.Graph.Operations.EdgeMat

@[expose] public section

/-!
# The adjacency at one choice of uncertain edge weights

[1]'s `A(λ)`: the fixed edges of `A` plus each uncertain edge's own weighted
contribution.

## Inputs
* `A` – adjacency matrix
* `U` – uncertain edges
* `lam` – weights of the uncertain edges

## Output
* adjacency matrix with the uncertain edges weighted by lam

## References

* [1] T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph Convolutional Networks
      with Uncertain Node Features and Uncertain Graph Structure". Transactions on Machine Learning
      Research, 2025.
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

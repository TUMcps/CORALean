module

public import CORALean.ContSet.ContSet.ContSet

@[expose] public section

/-!
# A node's degree in `Ã = A + I`

[1]'s `diag(1 Ã)` read at one node, as a column sum: `degree A j = ∑ i, (A + 1) i j`.
For the symmetric adjacency a graph convolution uses, rows and columns agree.

## Inputs
* `A` – adjacency matrix
* `j` – node

## Output
* degree of the node with self loops added

## References

* [1] T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph Convolutional Networks
      with Uncertain Node Features and Uncertain Graph Structure". Transactions on Machine Learning
      Research, 2025.
-/

-- Authors:       Claude Sonnet 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {N : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Node `j`'s degree in `Ã = A + I`, which is `diag(1 Ã)` read as a function. -/
def GNN.degree (A : Mat ℝ N N) (j : Fin N) : ℝ := ∑ i, (A + 1) i j

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

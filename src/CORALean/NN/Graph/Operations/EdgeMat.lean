module

public import CORALean.ContSet.ContSet.ContSet

@[expose] public section

/-!
# The 0/1 matrix one uncertain edge contributes

[1]'s uncertain graph structure, one edge at a time: `edgeMat` writes both
orientations at once, so an edge costs one factor and not two — the adjacency
a convolution reads is symmetric.

## Inputs
* `ij` – endpoints of the edge

## Output
* zero-one matrix with both orientations of the edge

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

variable {N : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The 0/1 matrix one undirected edge contributes, both orientations at once. -/
def GNN.edgeMat (ij : Fin N × Fin N) : Mat ℝ N N :=
  fun a b => if (a = ij.1 ∧ b = ij.2) ∨ (a = ij.2 ∧ b = ij.1) then 1 else 0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

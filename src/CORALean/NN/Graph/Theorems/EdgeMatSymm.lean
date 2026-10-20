module

public import CORALean.NN.Graph.Operations.EdgeMat

@[expose] public section

/-!
# `edgeMat` is symmetric

`edgeMat`'s `if` disjunct already lists both orientations of its one edge, so
swapping the two indices leaves the disjunction — and hence the value — the
same: the symmetry `[1, §4.3]`'s adjacency needs. Public rather than an
`aux_`: every caller of `edgeMat`, not only `AdjAtSymm`, needs this, and an
`aux_` would be invisible to them by construction.

## Inputs
* `ij` – endpoints of the edge
* `a` – row node
* `b` – column node

## Hypotheses
* none

## Conclusion
* the edge matrix is symmetric

## References

* [1] T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph
      Convolutional Networks with Uncertain Node Features and Uncertain Graph
      Structure". TMLR, 2025. arXiv:2404.15065.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {N : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `edgeMat` writes both orientations of its edge at once, so it is symmetric. -/
theorem GNN.edgeMat_symm (ij : Fin N × Fin N) (a b : Fin N) :
    GNN.edgeMat ij a b = GNN.edgeMat ij b a := by
  have h : ((a = ij.1 ∧ b = ij.2) ∨ (a = ij.2 ∧ b = ij.1)) ↔
      ((b = ij.1 ∧ a = ij.2) ∨ (b = ij.2 ∧ a = ij.1)) := by tauto
  simp only [GNN.edgeMat, h]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

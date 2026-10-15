module

public import CORALean.ContSet.ContSet.ContSet
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Logic.Equiv.Defs

@[expose] public section

/-!
# Permutation-invariant aggregations

[1, Def. 5]: a global pooling layer maps a graph's node-feature matrix `H ∈ ℝ^{|N|×c}` to one
feature vector by an aggregation `ψ` over the nodes, any `ψ` that is permutation invariant —
relabelling the nodes, permuting the rows of `H`, leaves `ψ(H)` unchanged. `PermInvariant ψ`
is that condition; the layer is `ψ` itself. Eq. (1)'s sum is one such `ψ`, `GNN.sumPoolLin`
(`sumPoolLin_permInvariant`), and the one the tree propagates sets through.

## References

* [1] T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph
      Convolutional Networks with Uncertain Node Features and Uncertain Graph
      Structure". TMLR, 2025. arXiv:2404.15065.
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      15-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {N F : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Def. 5]: `ψ` aggregates the nodes without regard to their order. -/
def GNN.PermInvariant (ψ : Mat ℝ N F → Vec ℝ F) : Prop :=
  ∀ (σ : Equiv.Perm (Fin N)) (H : Mat ℝ N F), ψ (H.submatrix σ id) = ψ H

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

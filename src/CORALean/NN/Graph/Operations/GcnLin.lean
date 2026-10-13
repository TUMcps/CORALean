module

public import CORALean.ContSet.ContSet.ContSet

@[expose] public section

/-!
# The graph convolutional layer as one linear map

CORA's `nnGCNLayer`, [1, Def. 4]: `H ↦ P H W`, `W` mixing features and `P` mixing
nodes. `P` and `W` stay separate arguments rather than one composed matrix: an
uncertain graph replaces `P` by an enclosure and leaves `W` alone.

## References

* [1] T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph
      Convolutional Networks with Uncertain Node Features and Uncertain Graph
      Structure". TMLR, 2025. arXiv:2404.15065.
-/

-- Authors:       Claude Sonnet 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {N F₁ F₂ : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The layer as one linear map: `W` mixes features, `P` mixes nodes. -/
def GNN.gcnLin (P : Mat ℝ N N) (W : Mat ℝ F₁ F₂) : Mat ℝ N F₁ →ₗ[ℝ] Mat ℝ N F₂ :=
  (matMulLeft P).comp (matMulRight W)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

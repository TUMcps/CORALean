module

public import CORALean.Global.ExactScalar

@[expose] public section

/-!
# The subgraph projection at a scalar, `[1, Cor. 1]`'s `M`

`selectMat 𝕋 κ` is `select κ` with its entries stored in `𝕋`: it places `1` and `0` only,
which every float format holds exactly, so it reads back as the real selection matrix
(`selectMat_toReal`).

## Inputs
* `𝕋` – scalar type
* `κ` – indices of the selected nodes

## Output
* rows of the identity matrix for the selected nodes

## References

* [1] T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph
      Convolutional Networks with Uncertain Node Features and Uncertain Graph
      Structure". TMLR, 2025. arXiv:2404.15065.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {𝕋 : Type} [Scalar 𝕋] [ExactScalar 𝕋] {N K : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The same matrix at any scalar: it places `1` and `0` only, which every float format holds
exactly, so `toRealMat (selectMat 𝕋 κ)` is `Real.GNN.select κ`. -/
def GNN.selectMat (𝕋 : Type) [Scalar 𝕋] [ExactScalar 𝕋] (κ : Fin K → Fin N) : Mat 𝕋 K N :=
  fun k i => if κ k = i then 1 else 0

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

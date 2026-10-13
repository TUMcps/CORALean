import CORALean.NN.Graph.Theorems.SelectMatToReal
import CORALean.NN.Graph.Theorems.SelectMul

/-!
# `selectMat` multiplies out to row selection

Row selection at any scalar: the stored matrix times the stored features, read as reals, is
`Matrix.submatrix`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Scalar

variable {𝕋 : Type} [Scalar 𝕋] [ExactScalar 𝕋] {N K F : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem GNN.selectMat_mul (κ : Fin K → Fin N) (H : Mat 𝕋 N F) :
    toRealMat (GNN.selectMat 𝕋 κ) * toRealMat H = (toRealMat H).submatrix κ id := by
  rw [GNN.selectMat_toReal, Real.GNN.select_mul]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

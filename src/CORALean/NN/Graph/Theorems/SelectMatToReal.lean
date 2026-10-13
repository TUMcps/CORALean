import CORALean.NN.Graph.Operations.SelectMat
import CORALean.NN.Graph.Operations.Select

/-!
# `selectMat` reads back as `select`

The matrix at a scalar `𝕋` denotes the real selection matrix.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Scalar

variable {𝕋 : Type} [Scalar 𝕋] [ExactScalar 𝕋] {N K : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem GNN.selectMat_toReal (κ : Fin K → Fin N) :
    toRealMat (GNN.selectMat 𝕋 κ) = Real.GNN.select κ := by -- --- PROOF ---
  funext k i
  rw [Scalar.toRealMat_apply]
  by_cases h : κ k = i
  · subst h
    simp [GNN.selectMat, Real.GNN.select, ExactScalar.toReal_one, Matrix.one_apply]
  · simp [GNN.selectMat, Real.GNN.select, h, ExactScalar.toReal_zero]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

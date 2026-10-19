module

public import CORALean.DiscrDynamics.MarkovChain.Theorems.ConvertTMem
public import CORALean.DiscrDynamics.MarkovChain.Theorems.GammaFullMem
public import CORALean.DiscrDynamics.MarkovChain.Theorems.ProjMatMulVec
public import CORALean.DiscrDynamics.MarkovChain.Operations.ConvertTransitionMatrix

@[expose] public section

/-!
# `convertTransitionMatrix` of a stochastic chain

The converted `T.T` and `T.OT` are column-stochastic when the chain is, and `GammaFull` is for
`γ > 0`; `projMat` marginalizes (`projMat_mulVec`).
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The three outputs of `convertTransitionMatrix` of a stochastic chain are column-stochastic. -/
theorem MarkovChain.convertTransitionMatrix_stochastic (M : MarkovChain n m) (h : M.IsStochastic)
    {γ : ℝ} (hγ : 0 < γ) : -- --- STMT ---
    (M.convertTransitionMatrix γ).T.T ∈
      Matrix.colStochastic ℝ (Fin (M.field.nrOfCells + 1) × Fin m) ∧
    (M.convertTransitionMatrix γ).T.OT ∈
      Matrix.colStochastic ℝ (Fin (M.field.nrOfCells + 1) × Fin m) ∧
    (M.convertTransitionMatrix γ).GammaFull ∈
      Matrix.colStochastic ℝ (Fin (M.field.nrOfCells + 1) × Fin m) :=
  ⟨MarkovChain.convertT_mem _ fun i => (h i).1, MarkovChain.convertT_mem _ fun i => (h i).2,
    MarkovChain.gammaFull_mem _ _ hγ⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

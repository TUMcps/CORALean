module

public import CORALean.DiscrDynamics.MarkovChain.Theorems.WithColumnColumn
public import CORALean.DiscrDynamics.MarkovChain.Theorems.TransitionProbabilitySum
public import CORALean.DiscrDynamics.MarkovChain.Operations.Build

@[expose] public section

/-!
# `build` writes a distribution

The column `build` sets, for a cell `iState ≠ 0` (the outside stays absorbing), consists of
nonnegative frequencies adding up to one, both after the time step and over it.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The column `build` sets, from nonempty sets of final states, is a distribution. -/
theorem MarkovChain.build_column (M : MarkovChain n m) (f : MarkovChain.FinalStates n)
    (iInput : Fin m) {iState : Fin (M.field.nrOfCells + 1)} (hs : iState ≠ 0) (hT : f.T ≠ [])
    (hOT : f.OT ≠ []) :
    ((∀ r, 0 ≤ (M.build f iInput iState).T.T iInput r iState) ∧
      ∑ r, (M.build f iInput iState).T.T iInput r iState = 1) ∧
    ((∀ r, 0 ≤ (M.build f iInput iState).T.OT iInput r iState) ∧
      ∑ r, (M.build f iInput iState).T.OT iInput r iState = 1) := by -- --- PROOF ---
  have hcol := MarkovChain.withColumn_column M ⟨MarkovChain.transitionProbability M.field f.T,
    MarkovChain.transitionProbability M.field f.OT⟩ iInput hs
  have hnn : ∀ (pts : List (Vec ℝ n)) (r : Fin (M.field.nrOfCells + 1)),
      0 ≤ MarkovChain.transitionProbability M.field pts r := fun pts r =>
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  -- `build` is `withColumn` of the empirical frequencies
  unfold MarkovChain.build
  refine ⟨⟨fun r => ?_, ?_⟩, ⟨fun r => ?_, ?_⟩⟩
  · rw [(hcol r).1]; exact hnn _ _
  · simp only [(hcol _).1]; exact MarkovChain.transitionProbability_sum _ hT
  · rw [(hcol r).2]; exact hnn _ _
  · simp only [(hcol _).2]; exact MarkovChain.transitionProbability_sum _ hOT

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

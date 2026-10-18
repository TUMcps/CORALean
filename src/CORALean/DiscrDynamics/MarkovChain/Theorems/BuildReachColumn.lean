module

public import CORALean.DiscrDynamics.MarkovChain.Theorems.WithColumnColumn
public import CORALean.DiscrDynamics.MarkovChain.Theorems.ReachProbabilityTSum
public import CORALean.DiscrDynamics.MarkovChain.Operations.BuildReach

@[expose] public section

/-!
# `build_reach` writes a column that conserves the weights

The column `buildReach` sets for a cell `iState ≠ 0` is `reachProbability`, whose entries add up
to the sum of the weights.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {n m : ℕ} {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [Real.IntervalOuter S]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The `T.T` column `buildReach` sets sums to the sum of the weights used. -/
theorem MarkovChain.buildReach_column_sum (M : MarkovChain n m)
    (R : List (MarkovChain.ReachEntry S n)) (iInput : Fin m)
    {iState : Fin (M.field.nrOfCells + 1)} (hs : iState ≠ 0) (tranFrac : List ℝ) : -- --- STMT ---
    ∑ r, (M.buildReach R iInput iState tranFrac).T.T iInput r iState =
      (tranFrac.take R.length).sum := by -- --- PROOF ---
  rw [← MarkovChain.reachProbability_T_sum M.field R tranFrac]
  exact Finset.sum_congr rfl fun r _ =>
    (MarkovChain.withColumn_column M _ iInput hs r).1

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

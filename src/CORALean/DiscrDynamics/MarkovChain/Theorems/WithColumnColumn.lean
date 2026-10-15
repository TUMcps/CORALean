module

public import CORALean.DiscrDynamics.MarkovChain.Operations.Basic
public import CORALean.DiscrDynamics.MarkovChain.Operations.WithColumn

@[expose] public section

/-!
# The column `withColumn` sets

For a cell other than the outside, column `iState` of the chosen input is the probabilities given,
in both matrices; only the outside column keeps `(1, 1) = 1` of its own.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Column `iState ≠ 0` of input `iInput` is `tp`, both for `T.T` and `T.OT`. -/
theorem MarkovChain.withColumn_column (M : MarkovChain n m)
    (tp : MarkovChain.TransitionProbabilities M.field.nrOfCells) (iInput : Fin m)
    {iState : Fin (M.field.nrOfCells + 1)} (hs : iState ≠ 0) (r : Fin (M.field.nrOfCells + 1)) :
    (M.withColumn tp iInput iState).T.T iInput r iState = tp.T r ∧
      (M.withColumn tp iInput iState).T.OT iInput r iState = tp.OT r := by -- --- PROOF ---
  simp [MarkovChain.withColumn, MarkovChain.setColumn, hs]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

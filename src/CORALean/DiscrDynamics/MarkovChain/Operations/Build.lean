module

public import CORALean.DiscrDynamics.MarkovChain.Operations.WithColumn

@[expose] public section

/-!
# `MarkovChain.build`

CORA's `build(Obj, finalStateMat, iInput, stateField)`: the transition probabilities out of cell
`stateField` under input `iInput`, from the cells the final states of simulated runs land in.
The runs themselves, random draws, are the caller's and enter as `finalStateMat`. The second
output `tp` is `transitionProbability` of the two point sets.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `build(Obj, finalStateMat, iInput, iState)`: the empirical cell frequencies as a column. -/
noncomputable def MarkovChain.build (M : MarkovChain n m)
    (finalStateMat : MarkovChain.FinalStates n) (iInput : Fin m)
    (iState : Fin (M.field.nrOfCells + 1)) : MarkovChain n m :=
  M.withColumn ⟨MarkovChain.transitionProbability M.field finalStateMat.T,
    MarkovChain.transitionProbability M.field finalStateMat.OT⟩ iInput iState

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

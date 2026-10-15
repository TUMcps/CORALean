module

public import CORALean.DiscrDynamics.MarkovChain.Operations.Basic

@[expose] public section

/-!
# `MarkovChain.withColumn`

The three lines `build` and `build_reach` share: column `iState + 1` of both `T{iInput}` is set
to the probabilities `tp` and entry `(1, 1)` to `1`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The chain with column `iState` of input `iInput` set to the probabilities `tp`. -/
def MarkovChain.withColumn (M : MarkovChain n m)
    (tp : MarkovChain.TransitionProbabilities M.field.nrOfCells) (iInput : Fin m)
    (iState : Fin (M.field.nrOfCells + 1)) : MarkovChain n m :=
  { field := M.field
    T :=
      { T := fun i => if i = iInput then MarkovChain.setColumn (M.T.T i) iState tp.T else M.T.T i
        OT := fun i =>
          if i = iInput then MarkovChain.setColumn (M.T.OT i) iState tp.OT else M.T.OT i } }

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

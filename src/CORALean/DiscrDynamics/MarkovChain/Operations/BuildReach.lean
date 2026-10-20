module

public import CORALean.DiscrDynamics.MarkovChain.Operations.ReachProbability
public import CORALean.DiscrDynamics.MarkovChain.Operations.WithColumn

@[expose] public section

/-!
# `MarkovChain.buildReach`

CORA's `build_reach(Obj, R, iInput, iState, tranFrac)`: the transition probabilities out of cell
`iState` under input `iInput`, from the reachable sets `R` instead of simulations. `tranFrac` is
the `tranFrac.TP` the function reads; the second output `tp` is `reachProbability`.

## Inputs
* `M` – Markov chain
* `R` – reach sets
* `iInput` – input index
* `iState` – cell index
* `tranFrac` – weights of the reach sets

## Output
* chain with the transition column from the reach sets
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {n m : ℕ} {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [Real.IntervalOuter S]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `build_reach(Obj, R, iInput, iState, tranFrac)`: the column from reachable-set volume shares. -/
noncomputable def MarkovChain.buildReach (M : MarkovChain n m)
    (R : List (MarkovChain.ReachEntry S n)) (iInput : Fin m)
    (iState : Fin (M.field.nrOfCells + 1)) (tranFrac : List ℝ) : MarkovChain n m :=
  M.withColumn (MarkovChain.reachProbability M.field R tranFrac) iInput iState

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

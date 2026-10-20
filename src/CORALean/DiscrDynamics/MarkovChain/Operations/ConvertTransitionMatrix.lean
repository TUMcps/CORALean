module

public import CORALean.DiscrDynamics.MarkovChain.Operations.Basic

@[expose] public section

/-!
# `MarkovChain.convertTransitionMatrix`

CORA's `convertTransitionMatrix(obj, gamma)`: the transition matrices of all inputs as one,
together with the projection from (cell, input) to cell and the input-mixing matrix
`GammaFull`. Pairs are ordered (cell, input), as CORA's `input + nrOfInputs (cell - 1)`.

## Inputs
* `M` – Markov chain
* `γ` – input mixing parameter

## Output
* chain with all inputs combined into one matrix
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `[T, projMat, GammaFull] = convertTransitionMatrix(obj, gamma)`. -/
noncomputable def MarkovChain.convertTransitionMatrix (M : MarkovChain n m) (γ : ℝ) :
    MarkovChain.Converted M.field.nrOfCells m where
  T := ⟨MarkovChain.convertT M.T.T, MarkovChain.convertT M.T.OT⟩
  projMat := MarkovChain.projMat M.field.nrOfCells m
  GammaFull := MarkovChain.gammaFull M.field.nrOfCells m γ

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.DiscrDynamics.MarkovChain.Definitions.Basic

@[expose] public section

/-!
# `MarkovChain.gamma`

The `Gamma` of CORA's `convertTransitionMatrix`: `1 / ((i - j)² + γ)` between inputs `i`
and `j`, `normalizeMatrix`-ed so that each column with a nonzero sum adds up to one.

## Inputs
* `m` – number of inputs
* `γ` – input mixing parameter

## Output
* normalized input mixing matrix
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `Gamma`: the input-to-input weights, normalized by column. -/
noncomputable def MarkovChain.gamma (m : ℕ) (γ : ℝ) : Matrix (Fin m) (Fin m) ℝ := fun i j =>
  let g := fun a b : Fin m => 1 / (((a : ℕ) - (b : ℕ) : ℝ) ^ 2 + γ)
  if ∑ k, g k j ≠ 0 then g i j / ∑ k, g k j else g i j

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.NN.Definitions.RefinableNetwork

@[expose] public section

/-!
# How many layers a schedule is read at

What a heuristic ranks over — a schedule is an infinite sequence and only its first `length`
entries are ever read.

## Inputs
* none

## Output
* number of layers
-/

-- Authors:       Claude Opus 5.5
-- Written:       05-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- How many levels a schedule is read at. -/
def RefinableNetwork.length : ∀ {n m : ℕ}, RefinableNetwork S n m → ℕ
  | _, _, .nil => 0
  | _, _, .cons _ rest => rest.length + 1

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

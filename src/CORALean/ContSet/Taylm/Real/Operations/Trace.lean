module

public import CORALean.ContSet.Taylm.Real.Operations.Basic

@[expose] public section

/-!
# `Taylm.trace`

CORA's `trace` of a square matrix of models: the sum of the diagonal, `obj(1,1) + obj(2,2) + …`.
Stored as a function from the two indices, as `Taylm.mtimes` stores its vector; the sum is
`Taylm.sum` (a right fold ending in the zero model), where CORA folds from the left starting at
`obj(1,1)`: the same sum, bracketed differently.

## Inputs
* `k` – matrix size
* `A` – matrix of models

## Output
* Taylor model of the trace
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.trace {k : ℕ} (A : Fin k → Fin k → Taylm n) : Taylm n :=
  Taylm.sum fun i => A i i

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

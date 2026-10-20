module

public import CORALean.ContSet.Taylm.Real.Operations.Mmul

@[expose] public section

/-!
# `Taylm.mpower`

CORA's `mpower` of a square array of models and a natural exponent (`@taylm/mpower.m`): for a
positive exponent `res = base; for i = 2:exponent, res = res * base`, for `0` the identity
matrix `eye`, a numeric matrix, here the constant models `0`/`1` (their order is irrelevant to
their enclosure). A scalar base is CORA's `power` (`Taylm.pow`); a non-square base or a
negative exponent is an error there, outside this definition.

## Inputs
* `k` – matrix size
* `A` – matrix of models

## Output
* function giving the matrix power for each exponent
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.mpower {k : ℕ} (A : Fin k → Fin k → Taylm n) : ℕ → Fin k → Fin k → Taylm n
  | 0 => fun i j => Taylm.const n (if i = j then 1 else 0) 0
  | e + 1 => (fun P => Taylm.mmul P A)^[e] A

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

import CORALean.ContSet.Taylm.Real.Operations.Times
import CORALean.ContSet.Taylm.Real.Operations.Sum

/-!
# `Taylm.mmul`

CORA's `mtimes` of two arrays of models, `@taylm/mtimes.m` with both factors Taylor models: entry
`(i, j)` is `Σₖ A i k .* B k j`, the loop CORA runs with `times` and `plus`.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.mmul {a b c : ℕ} (A : Fin a → Fin b → Taylm n) (B : Fin b → Fin c → Taylm n) :
    Fin a → Fin c → Taylm n :=
  fun i j => Taylm.sum fun k => (A i k).times (B k j)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

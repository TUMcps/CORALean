import CORALean.ContSet.Interval.Float.Interval

/-!
# `Interval.matResidual`

`Interval.residual` at `Mat 𝕋 m n`: the box an operation owes when it stores a
rounded matrix, entrywise `[lo - stored, hi - stored]`.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {m n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.matResidual (lo hi stored : Mat 𝕋 m n) : Interval (Mat 𝕋 m n) :=
  ⟨fun i j => subDown (lo i j) (stored i j), fun i j => subUp (hi i j) (stored i j)⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

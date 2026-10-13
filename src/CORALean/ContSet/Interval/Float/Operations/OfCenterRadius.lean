module

public import CORALean.ContSet.Interval.Float.Interval

@[expose] public section

/-!
# `Interval.ofCenterRadius`, over a floating-point scalar

CORA's constructor `intervalMatrix(C, Δ)`: the box `[C - Δ, C + Δ]` as an interval matrix, each
entry's lower bound rounded down and its upper bound up so the stored box contains the exact one.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {m n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.ofCenterRadius (c r : Mat 𝕋 m n) : Interval (Mat 𝕋 m n) where
  inf := fun i j => subDown (c i j) (r i j)
  sup := fun i j => addUp (c i j) (r i j)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

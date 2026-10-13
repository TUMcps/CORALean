module

public import CORALean.ContSet.Interval.Float.Interval

@[expose] public section

/-!
# `Interval.project`

The bounds at the chosen coordinates; nothing is computed, so nothing rounds.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.project (I : Interval (Vec 𝕋 n)) (dims : Fin m → Fin n) : Interval (Vec 𝕋 m) where
  inf := fun k => I.inf (dims k)
  sup := fun k => I.sup (dims k)


end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

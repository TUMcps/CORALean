module

public import CORALean.ContSet.Interval.Float.Interval

@[expose] public section

/-!
# `Interval.symmetric`

The box `[-r, r]`, which is what a bound known only in magnitude gives.
-/

-- Authors:       Claude Opus 5
-- Written:       16-August-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.symmetric (r : Vec 𝕋 n) : Interval (Vec 𝕋 n) := ⟨fun i => neg (r i), r⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

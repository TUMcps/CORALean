module

public import CORALean.ContSet.Taylm.Float.Taylm

@[expose] public section

/-!
# A constant Taylor model
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.const (n : ℕ) (c : 𝕋) (N : ℕ) : Taylm 𝕋 n := ⟨[(c, 0)], zero, zero, N⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

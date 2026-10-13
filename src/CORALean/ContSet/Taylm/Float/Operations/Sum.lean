import CORALean.ContSet.Taylm.Float.Operations.Plus

/-!
# `Taylm.sum`
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

def Taylm.sum : {m : ℕ} → (Fin m → Taylm 𝕋 n) → Taylm 𝕋 n
  | 0, _ => ⟨[], zero, zero, 0⟩
  | _ + 1, T => (T 0).plus (Taylm.sum fun i => T i.succ)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

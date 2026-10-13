module

public import CORALean.ContSet.Taylm.Float.Operations.Times

@[expose] public section

/-!
# `Taylm.prod`, over a floating-point scalar

The product folded from the left, `res = obj(1); res = res .* obj(i)`; at least one factor.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.prod : {m : ℕ} → (Fin (m + 1) → Taylm 𝕋 n) → Taylm 𝕋 n
  | 0, T => T 0
  | _ + 1, T => (Taylm.prod fun i => T i.castSucc).times (T (Fin.last _))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

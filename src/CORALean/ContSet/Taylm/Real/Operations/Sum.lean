import CORALean.ContSet.Taylm.Real.Operations.Plus

/-!
# `Taylm.sum`

CORA's `sum` of an array of models: `plus` folded from the right, the empty sum being the
zero model.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.sum : {m : ℕ} → (Fin m → Taylm n) → Taylm n
  | 0, _ => ⟨[], 0, 0, 0⟩
  | _ + 1, T => (T 0).plus (Taylm.sum fun i => T i.succ)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

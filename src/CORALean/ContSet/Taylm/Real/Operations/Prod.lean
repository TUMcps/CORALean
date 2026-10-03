import CORALean.ContSet.Taylm.Real.Operations.Times

/-!
# `Taylm.prod`

CORA's `prod` of an array of models along one dimension: `res = obj(1); for i = 2:m, res = res .*
obj(i)`, the product folded from the left. At least one factor: CORA's loop starts from the first
element and an empty array is an error, so the index type is `Fin (m + 1)`.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.prod : {m : ℕ} → (Fin (m + 1) → Taylm n) → Taylm n
  | 0, T => T 0
  | _ + 1, T => (Taylm.prod fun i => T i.castSucc).times (T (Fin.last _))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

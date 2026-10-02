import CORALean.ContSet.Taylm.Real.Taylm

/-!
# `Taylm.empty`

CORA's `empty(n)`: the model of the empty interval in each coordinate, a polynomial of
zero and the crossed remainder `[1, 0]`, which no function can satisfy.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.empty (n : ℕ) : Fin n → Taylm n :=
  fun _ => ⟨[], 1, 0, 0⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

import CORALean.Global.Float.SoundFloatArithmetic

/-!
# `MatExp.factorialUp`, a float upper bound of a factorial

`k!` copies of `one`, summed with `nsmulUp`: never below `k!` (`le_nsmulUp`), so
it is safe to divide by — `Theorems/InvFactorialBoundsFloat` is where that
division happens.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

def MatExp.factorialUp (k : ℕ) : 𝕋 := nsmulUp (Nat.factorial k) one

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

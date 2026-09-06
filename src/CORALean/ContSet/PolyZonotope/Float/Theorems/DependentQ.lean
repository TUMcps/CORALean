import CORALean.ContSet.PolyZonotope.Float.Operations.Dependent

/-!
# `dependent` has no independent generators left

Every one of them was made dependent.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

omit [SoundFloatArithmetic 𝕋] in
@[simp] theorem PolyZonotope.dependent_q (PZ : PolyZonotope 𝕋 n) : PZ.dependent.q = 0 := rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

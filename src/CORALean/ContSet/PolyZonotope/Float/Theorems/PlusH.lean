import CORALean.ContSet.PolyZonotope.Float.Operations.Plus

/-!
# `plus`'s dependent generator count is the sum of the two incoming ones
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
@[simp] theorem PolyZonotope.plus_h (pZ₁ pZ₂ : PolyZonotope (Vec 𝕋 n)) :
    (pZ₁.plus pZ₂).h = pZ₁.h + pZ₂.h := rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

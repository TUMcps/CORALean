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
@[simp] theorem PolyZonotope.plus_h (PZ₁ PZ₂ : PolyZonotope 𝕋 n) :
    (PZ₁.plus PZ₂).h = PZ₁.h + PZ₂.h := rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

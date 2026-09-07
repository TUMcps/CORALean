import CORALean.ContSet.PolyZonotope.Float.Operations.Plus

/-!
# `plus`'s independent generator count is the sum of the two incoming ones
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
@[simp] theorem PolyZonotope.plus_q (pZ₁ pZ₂ : PolyZonotope 𝕋 n) :
    (pZ₁.plus pZ₂).q = pZ₁.q + pZ₂.q := rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

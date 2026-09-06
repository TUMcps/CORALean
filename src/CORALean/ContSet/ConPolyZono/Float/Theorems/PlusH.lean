import CORALean.ContSet.ConPolyZono.Float.Operations.Plus

/-!
# `plus` does not change the total dependent generator count

The two blocks concatenate, so `h` adds.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

omit [SoundFloatArithmetic 𝕋] in
@[simp] theorem ConPolyZono.plus_h (C₁ C₂ : ConPolyZono 𝕋 n) :
    (C₁.plus C₂).h = C₁.h + C₂.h := rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

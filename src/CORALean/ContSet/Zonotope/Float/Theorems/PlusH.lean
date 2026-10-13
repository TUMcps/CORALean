module

public import CORALean.ContSet.Zonotope.Float.Operations.Plus

@[expose] public section

/-!
# `plus`'s generator count is the sum of the two incoming ones
-/

-- Authors:       Claude Opus 5
-- Written:       16-August-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

omit [SoundFloatArithmetic 𝕋] in
@[simp] theorem Zonotope.plus_h (Z₁ Z₂ : Zonotope (Vec 𝕋 n)) : (Z₁.plus Z₂).h = Z₁.h + Z₂.h := rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

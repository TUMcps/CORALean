import CORALean.ContSet.PolyZonotope.Float.Operations.LinComb

/-!
# `linComb`'s independent generator count is the sum of the two incoming ones

No fresh independent factor: the segment's own coefficient is dependent.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

omit [SoundFloatArithmetic 𝕋] in
@[simp] theorem PolyZonotope.linComb_q (pZ₁ pZ₂ : PolyZonotope (Vec 𝕋 n)) :
    (pZ₁.linComb pZ₂).q = pZ₁.q + pZ₂.q := rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

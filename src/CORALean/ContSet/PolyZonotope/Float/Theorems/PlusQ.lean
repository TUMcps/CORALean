import CORALean.ContSet.PolyZonotope.Float.Operations.Plus

/-!
# `plus`'s independent generator count is the sum of the two incoming ones
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

omit [SoundFloatArithmetic 𝕋] in
@[simp] theorem PolyZonotope.plus_q (PZ₁ PZ₂ : PolyZonotope 𝕋 n) :
    (PZ₁.plus PZ₂).q = PZ₁.q + PZ₂.q := rfl

end CORALean.Float

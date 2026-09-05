import CORALean.ContSet.PolyZonotope.Float.Operations.LinComb

/-!
# `linComb`'s dependent generator count

The two incoming blocks, plus the fresh segment block the same size again.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

omit [SoundFloatArithmetic 𝕋] in
@[simp] theorem PolyZonotope.linComb_h (PZ₁ PZ₂ : PolyZonotope 𝕋 n) :
    (PZ₁.linComb PZ₂).h = PZ₁.h + PZ₂.h + (PZ₁.h + PZ₂.h + 1) := rfl

end CORALean.Float

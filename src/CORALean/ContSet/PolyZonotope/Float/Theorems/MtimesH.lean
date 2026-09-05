import CORALean.ContSet.PolyZonotope.Float.Operations.Mtimes

/-!
# `mtimes` does not change the dependent generator count
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}

omit [SoundFloatArithmetic 𝕋] in
@[simp] theorem PolyZonotope.mtimes_h (M : Mat 𝕋 m n) (PZ : PolyZonotope 𝕋 n) :
    (PolyZonotope.mtimes M PZ).h = PZ.h := rfl

end CORALean.Float

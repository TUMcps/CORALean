import CORALean.ContSet.ConPolyZono.Float.Operations.Mtimes

/-!
# `mtimes` does not change the dependent generator count

The image is read off the same factor vectors, so nothing about the dependent
block's shape moves.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---

namespace CORALean.Float

open Pointwise Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n k : ℕ}

omit [SoundFloatArithmetic 𝕋] in
@[simp] theorem ConPolyZono.mtimes_h (M : Mat 𝕋 k n) (C : ConPolyZono 𝕋 n) :
    (ConPolyZono.mtimes M C).h = C.h := rfl

end CORALean.Float

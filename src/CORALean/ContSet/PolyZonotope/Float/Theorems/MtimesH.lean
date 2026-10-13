import CORALean.ContSet.PolyZonotope.Float.Operations.Mtimes

/-!
# `mtimes` does not change the dependent generator count
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

omit [SoundFloatArithmetic 𝕋] in
@[simp] theorem PolyZonotope.mtimes_h (M : Mat 𝕋 m n) (pZ : PolyZonotope (Vec 𝕋 n)) :
    (PolyZonotope.mtimes M pZ).h = pZ.h := rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

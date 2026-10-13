module

public import CORALean.ContSet.Zonotope.Float.Operations.Mtimes

@[expose] public section

/-!
# `mtimes` does not change the generator count
-/

-- Authors:       Claude Opus 5
-- Written:       16-August-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

omit [SoundFloatArithmetic 𝕋] in
@[simp] theorem Zonotope.mtimes_h (M : Mat 𝕋 m n) (Z : Zonotope (Vec 𝕋 n)) :
    (Zonotope.mtimes M Z).h = Z.h := rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

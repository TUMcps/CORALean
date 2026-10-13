module

public import CORALean.ContSet.Zonotope.Float.Operations.AbsorbError

@[expose] public section

/-!
# `absorbError` spends the box as `n` fresh generators
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
@[simp] theorem Zonotope.absorbError_h (Z : Zonotope (Vec 𝕋 n)) : Z.absorbError.h = Z.h + n := rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

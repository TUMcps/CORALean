import CORALean.ContSet.ProbZonotope.Float.ProbZonotope

/-!
# `ProbZonotope.mean`, over a floating-point scalar

The zonotope of possible means: the stored mean zonotope.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ProbZonotope.mean (P : ProbZonotope 𝕋 n) : Zonotope (Vec 𝕋 n) := P.Z
end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

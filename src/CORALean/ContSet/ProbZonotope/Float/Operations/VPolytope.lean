import CORALean.ContSet.ProbZonotope.Float.ProbZonotope
import CORALean.ContSet.Conversion.Float.Zonotope_to_VPolytope

/-!
# `ProbZonotope.vPolytope`, over a floating-point scalar

CORA's `polytope(zonotope(probZ.Z))`: the corner polytope of the mean zonotope; the covariance
plays no part.
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

def ProbZonotope.vPolytope (P : ProbZonotope 𝕋 n) : VPolytope (Vec 𝕋 n) := P.Z.vPolytope
end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

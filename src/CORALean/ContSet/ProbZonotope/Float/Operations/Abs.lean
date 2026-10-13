import CORALean.ContSet.ProbZonotope.Float.ProbZonotope
import CORALean.ContSet.Zonotope.Float.Operations.Abs

/-!
# `ProbZonotope.abs`, over a floating-point scalar

CORA's `abs(probZ)`: the mean zonotope becomes the float `Zonotope.abs` of itself (centre column
and generators in absolute value, exact) and the covariance interval is kept. As at the real
layer this is a different set of laws, not an enclosure of the input's.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ProbZonotope.abs (P : ProbZonotope 𝕋 n) : ProbZonotope 𝕋 n :=
  ⟨P.Z.abs, P.cov⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

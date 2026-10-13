import CORALean.ContSet.Conversion.Float.ConZonotope_to_Zonotope
import CORALean.ContSet.Conversion.Float.Zonotope_to_ConZonotope
import CORALean.ContSet.Zonotope.Float.Operations.Reduce

/-!
# `ConZonotope.reduce`

Above the requested order, the enclosing zonotope is reduced and the constraints
dropped; at or below it, nothing happens and the constraints survive. As over ℝ.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   08-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ConZonotope.reduce (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) (o : ℕ) : ConZonotope 𝕋 (Vec 𝕋 n) :=
  if o * n < cZ.h then (cZ.zonotope.reduce o).conZonotope else cZ

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

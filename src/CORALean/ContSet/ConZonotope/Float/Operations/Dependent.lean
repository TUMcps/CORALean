import CORALean.ContSet.ConZonotope.Float.ConZonotope
import CORALean.ContSet.PolyZonotope.Float.Operations.ErrorBound
import CORALean.ContSet.HPolytope.Float.Operations.PadLeft

/-!
# `ConZonotope.dependent`

The error box made into coefficients: one fresh generator per coordinate, as long as the box's
larger endpoint (`errorBound`, which rounds nothing), on a coefficient the constraints leave
free. A quadratic map is not additive, so a nominal part and a box cannot travel through it
separately; emptying the box first is what `quadMap` needs, as for `PolyZonotope.dependent`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ConZonotope.dependent (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) : ConZonotope 𝕋 (Vec 𝕋 n) where
  h := cZ.h + n
  c := cZ.c
  G := Fin.append cZ.G (diagonalBlock (PolyZonotope.errorBound cZ.E))
  P := cZ.P.padLeft n
  E := ⟨fun _ => zero, fun _ => zero⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

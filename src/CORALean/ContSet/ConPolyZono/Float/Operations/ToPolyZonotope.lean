import CORALean.ContSet.ConPolyZono.Float.ConPolyZono
import CORALean.ContSet.PolyZonotope.Float.PolyZonotope

/-!
# `ConPolyZono.toPolyZonotope`, over a floating-point scalar

The generator data on its own, the constraint system left behind: the same fields, the same error
box.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ConPolyZono.toPolyZonotope (cPZ : ConPolyZono 𝕋 n) : PolyZonotope 𝕋 n where
  p := cPZ.p
  h := cPZ.h
  q := cPZ.q
  c := cPZ.c
  G := cPZ.G
  E := cPZ.E
  GI := cPZ.GI
  err := cPZ.err

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

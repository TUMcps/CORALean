module

public import CORALean.ContSet.ConPolyZono.Float.ConPolyZono
public import CORALean.ContSet.PolyZonotope.Float.PolyZonotope

@[expose] public section

/-!
# `ConPolyZono.toPolyZonotope`, over a floating-point scalar

The generator data on its own, the constraint system left behind: the same fields, the same error
box.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ConPolyZono.toPolyZonotope (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) : PolyZonotope (Vec 𝕋 n) where
  p := cPZ.p
  h := cPZ.h
  q := cPZ.qI
  c := cPZ.c
  G := cPZ.G
  E := cPZ.E
  GI := cPZ.GI
  I_error := cPZ.I_error

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

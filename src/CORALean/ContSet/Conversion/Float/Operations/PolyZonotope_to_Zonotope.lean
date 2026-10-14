module

public import CORALean.ContSet.Conversion.Float.Operations.ConPolyZono_to_PolyZonotope
public import CORALean.ContSet.PolyZonotope.Real.Theorems.AbsMonomialLeOne
public import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.PolyZonotope_to_Zonotope

@[expose] public section

/-!
# A polynomial zonotope as a zonotope, over a floating-point scalar
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The dependent generators, then the independent ones, side by side. -/
def PolyZonotope.zonotope (pZ : PolyZonotope (Vec 𝕋 n)) : Zonotope (Vec 𝕋 n) where
  h := pZ.h + pZ.q
  c := pZ.c
  G := Fin.append pZ.G pZ.GI
  I_error := pZ.I_error

def ConPolyZono.zonotope (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) : Zonotope (Vec 𝕋 n) :=
  cPZ.polyZonotope.zonotope

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

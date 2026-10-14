module

public import CORALean.ContSet.Conversion.Float.Operations.PolyZonotope_to_Zonotope
public import CORALean.ContSet.Conversion.Float.Operations.Basic
public import CORALean.ContSet.Conversion.Float.Operations.ConPolyZono_to_PolyZonotope
public import CORALean.ContSet.Conversion.Real.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.PolyZonotope_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_ConZonotope

@[expose] public section

/-!
# A polynomial zonotope as a zonotope, and a constrained one as a constrained
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

def PolyZonotope.conZonotope (pZ : PolyZonotope (Vec 𝕋 n)) : ConZonotope 𝕋 (Vec 𝕋 n) :=
  pZ.zonotope.conZonotope

def ConPolyZono.conZonotope (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) : ConZonotope 𝕋 (Vec 𝕋 n) :=
  cPZ.polyZonotope.conZonotope

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

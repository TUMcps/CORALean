module

public import CORALean.ContSet.Conversion.Float.PolyZonotope_to_Zonotope
public import CORALean.ContSet.Conversion.Float.ConZonotope_to_Zonotope
public import CORALean.ContSet.Conversion.Float.Zonotope_to_ConZonotope

@[expose] public section

/-!
# A polynomial zonotope as a zonotope, and a constrained one as a constrained — the construction

`PolyZonotope.conZonotope` and `ConPolyZono.conZonotope` are the constructions;
`PolyZonotope_to_ConZonotope` states and proves what they guarantee.
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

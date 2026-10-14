module

public import CORALean.ContSet.Conversion.Float.Ellipsoid_to_Interval
public import CORALean.ContSet.Conversion.Float.Interval_to_PolyZonotope

@[expose] public section

/-!
# An ellipsoid as a polynomial zonotope, over a floating-point scalar — the construction

`Ellipsoid.polyZonotope` is the construction; `Ellipsoid_to_PolyZonotope` states and proves what it
guarantees.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Ellipsoid.polyZonotope (E : Ellipsoid 𝕋 n) (s : Vec 𝕋 n) : PolyZonotope (Vec 𝕋 n) :=
  (E.interval s).polyZonotope

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

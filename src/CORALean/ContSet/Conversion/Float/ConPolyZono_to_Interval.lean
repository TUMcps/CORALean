import CORALean.ContSet.Conversion.Float.ConPolyZono_to_PolyZonotope
import CORALean.ContSet.Conversion.Float.PolyZonotope_to_Interval

/-!
# A constrained polynomial zonotope as a box, over a floating-point scalar

Through the polynomial zonotope, dropping the constraints, then its box.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

def ConPolyZono.interval (cPZ : ConPolyZono 𝕋 n) : Interval (Vec 𝕋 n) :=
  cPZ.polyZonotope.interval

variable [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.interval_contains (cPZ : ConPolyZono 𝕋 n) :
    cPZ.construct ⊆ cPZ.interval.construct :=
  subset_trans cPZ.polyZonotope_contains cPZ.polyZonotope.interval_contains

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

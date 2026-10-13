module

public import CORALean.ContSet.Conversion.Float.Interval_to_PolyZonotope
public import CORALean.ContSet.Conversion.Float.PolyZonotope_to_ConPolyZono

@[expose] public section

/-!
# A box as a constrained polynomial zonotope, over a floating-point scalar

Through the polynomial zonotope, the box riding in `err`: nothing rounds.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

def Interval.conPolyZono (I : Interval (Vec 𝕋 n)) : ConPolyZono 𝕋 (Vec 𝕋 n) :=
  I.polyZonotope.conPolyZono

variable [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.conPolyZono_contains (I : Interval (Vec 𝕋 n)) :
    I.construct ⊆ I.conPolyZono.construct :=
  subset_trans I.polyZonotope_contains I.polyZonotope.conPolyZono_contains

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

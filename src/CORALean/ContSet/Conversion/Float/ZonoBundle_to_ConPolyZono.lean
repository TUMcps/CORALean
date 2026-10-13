module

public import CORALean.ContSet.Conversion.Float.Zonotope_to_ConPolyZono
public import CORALean.ContSet.Conversion.Float.ZonoBundle_to_Zonotope

@[expose] public section

/-!
# A zonoBundle as a constrained polynomial zonotope, over a floating-point scalar

Any one member, converted, holds the bundle: nothing rounds.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

def ZonoBundle.conPolyZono (zB : ZonoBundle (Vec 𝕋 n)) (i : Fin zB.k) : ConPolyZono 𝕋 (Vec 𝕋 n) :=
  (zB.zonotope i).conPolyZono

variable [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.conPolyZono_contains (zB : ZonoBundle (Vec 𝕋 n)) (i : Fin zB.k) :
    zB.construct ⊆ (zB.conPolyZono i).construct :=
  subset_trans (zB.zonotope_contains i) (zB.zonotope i).conPolyZono_contains

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

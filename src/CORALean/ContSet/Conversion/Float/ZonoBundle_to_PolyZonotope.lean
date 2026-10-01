import CORALean.ContSet.Conversion.Float.Zonotope_to_PolyZonotope
import CORALean.ContSet.Conversion.Float.ZonoBundle_to_Zonotope

/-!
# A zonoBundle as a polynomial zonotope, over a floating-point scalar

The bundle is the intersection of its members, so any one member, converted, holds
it: nothing rounds.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

def ZonoBundle.polyZonotope (zB : ZonoBundle 𝕋 n) (i : Fin zB.k) : PolyZonotope 𝕋 n :=
  (zB.zonotope i).polyZonotope

variable [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.polyZonotope_contains (zB : ZonoBundle 𝕋 n) (i : Fin zB.k) :
    zB.construct ⊆ (zB.polyZonotope i).construct :=
  subset_trans (zB.zonotope_contains i) (zB.zonotope i).polyZonotope_contains

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

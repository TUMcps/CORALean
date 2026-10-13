module

public import CORALean.ContSet.Conversion.Float.Zonotope_to_PolyZonotope
public import CORALean.ContSet.Conversion.Float.ZonoBundle_to_Zonotope

@[expose] public section

/-!
# A zonoBundle as a polynomial zonotope, over a floating-point scalar

The bundle is the intersection of its members, so any one member, converted, holds
it: nothing rounds.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

def ZonoBundle.polyZonotope (zB : ZonoBundle (Vec 𝕋 n)) (i : Fin zB.k) : PolyZonotope (Vec 𝕋 n) :=
  (zB.zonotope i).polyZonotope

variable [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.polyZonotope_contains (zB : ZonoBundle (Vec 𝕋 n)) (i : Fin zB.k) :
    zB.construct ⊆ (zB.polyZonotope i).construct :=
  subset_trans (zB.zonotope_contains i) (zB.zonotope i).polyZonotope_contains

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

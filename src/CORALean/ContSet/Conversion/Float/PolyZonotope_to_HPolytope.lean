module

public import CORALean.ContSet.Conversion.Float.PolyZonotope_to_Zonotope
public import CORALean.ContSet.Conversion.Float.Zonotope_to_HPolytope

@[expose] public section

/-!
# A polynomial zonotope as halfspaces, over a floating-point scalar

Through the zonotope enclosure, then that zonotope's own rounded support bounds; the rows
are the caller's, as in `Zonotope.hPolytope_contains`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n q : ℕ}

def PolyZonotope.hPolytope (pZ : PolyZonotope (Vec 𝕋 n)) (Aq : Mat 𝕋 q n) : HPolytope 𝕋 (Vec 𝕋 n) :=
  pZ.zonotope.hPolytope Aq


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.hPolytope_contains (pZ : PolyZonotope (Vec 𝕋 n)) (Aq : Mat 𝕋 q n) :
    pZ.construct ⊆ (pZ.hPolytope Aq).construct :=
  subset_trans pZ.zonotope_contains (Zonotope.hPolytope_contains _ _)


end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

import CORALean.ContSet.Conversion.Float.ConZonotope_to_Zonotope
import CORALean.ContSet.Conversion.Float.Zonotope_to_HPolytope

/-!
# A constrained zonotope as halfspaces, over a floating-point scalar

Constraints dropped, then the zonotope answers each direction by summing
absolute values with directed rounding.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n q : ℕ}

def ConZonotope.hPolytope (cZ : ConZonotope 𝕋 n) (Aq : Mat 𝕋 q n) : HPolytope 𝕋 n :=
  cZ.zonotope.hPolytope Aq


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.hPolytope_contains (cZ : ConZonotope 𝕋 n) (Aq : Mat 𝕋 q n) :
    cZ.construct ⊆ (cZ.hPolytope Aq).construct :=
  subset_trans cZ.zonotope_contains (Zonotope.hPolytope_contains _ _)


end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

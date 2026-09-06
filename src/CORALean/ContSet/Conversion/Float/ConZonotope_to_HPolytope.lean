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

def ConZonotope.hPolytope (C : ConZonotope 𝕋 n) (Aq : Mat 𝕋 q n) : HPolytope 𝕋 n :=
  C.zonotope.hPolytope Aq


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.subset_hPolytope (C : ConZonotope 𝕋 n) (Aq : Mat 𝕋 q n) :
    C.construct ⊆ (C.hPolytope Aq).construct :=
  subset_trans C.zonotope_outer (Zonotope.subset_hPolytope _ _)


end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

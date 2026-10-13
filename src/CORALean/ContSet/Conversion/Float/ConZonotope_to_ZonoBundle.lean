import CORALean.ContSet.Conversion.Float.ConZonotope_to_Zonotope
import CORALean.ContSet.Conversion.Float.Zonotope_to_ZonoBundle

/-!
# A constrained zonotope as a bundle of one, over a floating-point scalar

Through `ConZonotope.zonotope`, which drops the constraints, then
`Zonotope.zonoBundle`, the single-member bundle, exact. All the loss is the
first leg's.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

def ConZonotope.zonoBundle (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) : ZonoBundle (Vec 𝕋 n) :=
  cZ.zonotope.zonoBundle


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.zonoBundle_contains (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) :
    cZ.construct ⊆ cZ.zonoBundle.construct :=
  subset_trans cZ.zonotope_contains (Zonotope.zonoBundle_exact _).subset

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

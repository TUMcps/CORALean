import CORALean.ContSet.Conversion.Float.VPolytope_to_Zonotope
import CORALean.ContSet.Conversion.Float.Zonotope_to_ZonoBundle

/-!
# A vertex description as a bundle of one, over a floating-point scalar

Through the zonotope the box gives, then `Zonotope.zonoBundle`, exact. All the
loss is the box route's.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

def VPolytope.zonoBundle (P : VPolytope (Vec 𝕋 n)) : ZonoBundle (Vec 𝕋 n) :=
  P.zonotope.zonoBundle


-- =======================================  MAIN THEOREM  ======================================= --

theorem VPolytope.zonoBundle_contains (P : VPolytope (Vec 𝕋 n)) :
    P.construct ⊆ P.zonoBundle.construct :=
  subset_trans P.zonotope_contains (Zonotope.zonoBundle_exact _).subset

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

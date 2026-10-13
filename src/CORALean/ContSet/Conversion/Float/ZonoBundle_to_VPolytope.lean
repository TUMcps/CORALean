import CORALean.ContSet.Conversion.Float.ZonoBundle_to_Zonotope
import CORALean.ContSet.Conversion.Float.Zonotope_to_VPolytope

/-!
# A bundle's corners, at one component, over a floating-point scalar

Through `ZonoBundle.zonotope i`, then that zonotope's own sign corners.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

def ZonoBundle.vPolytope (zB : ZonoBundle (Vec 𝕋 n)) (i : Fin zB.k) : VPolytope (Vec 𝕋 n) :=
  (zB.zonotope i).vPolytope


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.vPolytope_contains (zB : ZonoBundle (Vec 𝕋 n)) (i : Fin zB.k) :
    zB.construct ⊆ (zB.vPolytope i).construct :=
  subset_trans (zB.zonotope_contains i) (Zonotope.vPolytope_contains _)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

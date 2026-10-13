import CORALean.ContSet.Conversion.Float.ZonoBundle_to_Zonotope
import CORALean.ContSet.Conversion.Float.Zonotope_to_HPolytope

/-!
# A bundle's halfspaces, at one component, over a floating-point scalar

Through `ZonoBundle.zonotope i`, then that zonotope's own halfspace description
in the directions the caller names.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

def ZonoBundle.hPolytope {q : ℕ} (zB : ZonoBundle (Vec 𝕋 n)) (i : Fin zB.k) (Aq : Mat 𝕋 q n) :
    HPolytope 𝕋 (Vec 𝕋 n) :=
  (zB.zonotope i).hPolytope Aq


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.hPolytope_contains {q : ℕ} (zB : ZonoBundle (Vec 𝕋 n)) (i : Fin zB.k)
    (Aq : Mat 𝕋 q n) : zB.construct ⊆ (zB.hPolytope i Aq).construct :=
  subset_trans (zB.zonotope_contains i) (Zonotope.hPolytope_contains _ _)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

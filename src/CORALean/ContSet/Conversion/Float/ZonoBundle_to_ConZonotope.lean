import CORALean.ContSet.Conversion.Float.ZonoBundle_to_Zonotope
import CORALean.ContSet.Conversion.Float.Zonotope_to_ConZonotope

/-!
# A bundle's constrained zonotope, at one component, over a floating-point scalar

Through `ZonoBundle.zonotope i`, then the constrained zonotope with nothing to
satisfy. Whichever component `i` names, the guarantee holds.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

def ZonoBundle.conZonotope (zB : ZonoBundle 𝕋 n) (i : Fin zB.k) : ConZonotope 𝕋 n :=
  (zB.zonotope i).conZonotope


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.conZonotope_contains (zB : ZonoBundle 𝕋 n) (i : Fin zB.k) :
    zB.construct ⊆ (zB.conZonotope i).construct :=
  subset_trans (zB.zonotope_contains i) (Zonotope.conZonotope_contains _)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

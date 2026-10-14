module

public import CORALean.ContSet.Conversion.Float.ZonoBundle_to_Zonotope
public import CORALean.ContSet.Conversion.Float.Zonotope_to_VPolytope

@[expose] public section

/-!
# A bundle's corners, at one component, over a floating-point scalar — the construction

`ZonoBundle.vPolytope` is the construction; `ZonoBundle_to_VPolytope` states and proves what it
guarantees.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ZonoBundle.vPolytope (zB : ZonoBundle (Vec 𝕋 n)) (i : Fin zB.k) : VPolytope (Vec 𝕋 n) :=
  (zB.zonotope i).vPolytope

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

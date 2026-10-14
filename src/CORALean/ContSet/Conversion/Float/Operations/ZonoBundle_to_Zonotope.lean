module

public import CORALean.ContSet.ZonoBundle.Float.ZonoBundle

@[expose] public section

/-!
# One component of a bundle, enclosing it, over a floating-point scalar — the construction

`ZonoBundle.zonotope` is the construction; `ZonoBundle_to_Zonotope` states and proves what it
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

def ZonoBundle.zonotope (zB : ZonoBundle (Vec 𝕋 n)) (i : Fin zB.k) : Zonotope (Vec 𝕋 n) := zB.Z i

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

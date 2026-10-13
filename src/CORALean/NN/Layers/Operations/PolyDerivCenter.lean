module

public import CORALean.Global.Float.FloatOps

@[expose] public section

/-!
# A stored fit's derivative centre

The fit's linear coefficient, copied and so stored exactly; below order 1 there is none, and the
centre is zero.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The fit's linear coefficient, `zero` below order 1. -/
def polyDerivCenter (c : Fin (n + 1) → 𝕋) : 𝕋 := if h : 1 < n + 1 then c ⟨1, h⟩ else zero

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

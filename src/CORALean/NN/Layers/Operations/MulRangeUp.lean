module

public import CORALean.Global.Float.FloatOps

@[expose] public section

/-!
# A product over a bracket, from above

The mirror of `mulRangeDown`: both products rounded up and the larger.
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

/-- And from above, the same two products the other way. -/
def mulRangeUp (a lo hi : 𝕋) : 𝕋 := maximum (mulUp a lo) (mulUp a hi)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

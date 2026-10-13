import CORALean.Global.Float.FloatOps

/-!
# The sampled range's upper end

The greatest sampled value, raised by that same slack.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {N : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The greatest sampled value, raised by the slack rounded up. -/
def sampleHi (gUp : Fin (N + 1) → 𝕋) (M dx : 𝕋) : 𝕋 := addUp (maximumOver gUp) (mulUp M dx)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

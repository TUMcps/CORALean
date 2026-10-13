module

public import CORALean.Global.Float.FloatOps

@[expose] public section

/-!
# The recentring a bracket asks for

The bracket's two ends averaged, `half` being exact and the rounding all in the `addUp`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The midpoint of a bracket. -/
def bracketShift (lo hi : 𝕋) : 𝕋 := half (addUp lo hi)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

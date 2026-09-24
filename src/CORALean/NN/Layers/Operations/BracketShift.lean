import CORALean.Global.Float.FloatOps

/-!
# The recentring a bracket asks for

The bracket's two ends averaged, `half` being exact and the rounding all in the `addUp`.
-/

-- Authors:       Tobias Ladner
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The midpoint of a bracket. -/
def bracketShift (lo hi : 𝕋) : 𝕋 := half (addUp lo hi)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

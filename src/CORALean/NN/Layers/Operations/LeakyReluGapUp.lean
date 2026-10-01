import CORALean.NN.Layers.Operations.LeakyReluEndUp

/-!
# Leaky ReLU above a line, over a box

Leaky ReLU is convex, so its gap above a line is the larger of its two end values.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The larger of the two ends: the gap over `[l, u]`, by convexity. -/
def leakyReluGapUp (α m l u : 𝕋) : 𝕋 := maximum (leakyReluEndUp α m l) (leakyReluEndUp α m u)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

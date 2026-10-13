import CORALean.NN.Layers.Definitions.Relaxation
import CORALean.NN.Layers.Operations.ClampUnit
import CORALean.NN.Layers.Operations.ReluGapUp

/-!
# The ReLU relaxation at a chosen slope

Convexity gives the whole relaxation: ReLU lies above any line of slope in `[0, 1]` through the
origin and below it raised by the gap, so the relaxation at a clamped slope is that line
recentred, `± gap / 2`. Halving only moves the exponent, so only the gap rounds, and up.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

-- not `Matrix`: its `zero` would make `FloatOps.zero` ambiguous
open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Recentred, so that the error is half the gap in each direction. -/
def reluRelaxation (lam : 𝕋 → 𝕋 → 𝕋) : Relaxation 𝕋 where
  slope l u := clampUnit (lam l u)
  offset l u := half (reluGapUp (clampUnit (lam l u)) l u)
  error l u := half (reluGapUp (clampUnit (lam l u)) l u)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

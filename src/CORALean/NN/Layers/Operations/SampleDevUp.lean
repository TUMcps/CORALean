import CORALean.NN.Layers.Definitions.Enclosure
import CORALean.NN.Layers.Operations.EvalPolyDown

/-!
# The deviation of σ from a fit at a sample, from above

The other crossing: the activation's high end against the fit's low one.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- And from above, the other crossing. -/
def sampleDevUp (E : Enclosure 𝕋) (c : Fin (m + 1) → 𝕋) (x : 𝕋) : 𝕋 :=
  subUp (E.hi x) (evalPolyDown c x)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

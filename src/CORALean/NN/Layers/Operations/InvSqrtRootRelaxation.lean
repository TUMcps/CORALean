import CORALean.NN.Layers.Operations.InvSqrtRootEnclosure
import CORALean.NN.Layers.Operations.RelaxationOfAntitone

/-!
# The inverse square root relaxation (machine)

The slope-zero relaxation of the antitone `invSqrt` at `invSqrtRootEnclosure`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The slope-zero relaxation of an antitone function at that enclosure. -/
def invSqrtRootRelaxation (p : ℕ) : Relaxation 𝕋 := Relaxation.ofAntitone (invSqrtRootEnclosure p)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

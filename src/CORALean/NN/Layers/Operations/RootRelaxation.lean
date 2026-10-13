module

public import CORALean.NN.Layers.Operations.RootEnclosure
public import CORALean.NN.Layers.Operations.RelaxationOfMonotone

@[expose] public section

/-!
# The square root relaxation

The slope-zero relaxation of the monotone square root at `rootEnclosure`.
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

/-- The slope-zero relaxation of a monotone function at that enclosure. -/
def rootRelaxation (p : ℕ) : Relaxation 𝕋 := Relaxation.ofMonotone (rootEnclosure p)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

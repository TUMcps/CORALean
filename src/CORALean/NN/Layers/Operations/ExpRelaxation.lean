module

public import CORALean.NN.Layers.Operations.ExpEnclosure
public import CORALean.NN.Layers.Operations.RelaxationOfMonotone

@[expose] public section

/-!
# The exponential relaxation

`Relaxation.ofMonotone` at `expEnclosure`, CORA's `nnExpLayer` read as the monotone relaxation,
slope zero.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The slope-zero relaxation of a monotone function at that enclosure. -/
def expRelaxation (k : ℕ) : Relaxation 𝕋 := Relaxation.ofMonotone (expEnclosure k)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

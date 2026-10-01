import CORALean.NN.Layers.Operations.ExpEnclosure
import CORALean.NN.Layers.Operations.RelaxationOfMonotone

/-!
# The exponential relaxation

`Relaxation.ofMonotone` at `expEnclosure`, CORA's `nnExpLayer` read as the monotone relaxation,
slope zero.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The slope-zero relaxation of a monotone function at that enclosure. -/
def expRelaxation (k : ℕ) : Relaxation 𝕋 := Relaxation.ofMonotone (expEnclosure k)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

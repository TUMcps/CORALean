import CORALean.NN.Layers.Operations.PolyRelaxationToRelaxation
import CORALean.NN.Layers.Operations.RelaxationToPoly

/-!
# Order 1 is a reading of an affine relaxation

The two round-trip by `rfl`, which is what makes "order 1" a reading of `Relaxation` rather
than a second notion standing beside it.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Relaxation.toPoly_toRelaxation (R : Relaxation 𝕋) :
    R.toPoly.toRelaxation = R := rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.NN.Layers.Operations.RelaxationOfMonotone
public import CORALean.NN.Layers.Operations.RelaxationTighter
public import CORALean.NN.Layers.Operations.Basic
public import CORALean.NN.Layers.Operations.SigmoidEnclosure

@[expose] public section

/-!
# The sigmoid relaxation

The curvature relaxation where its bracket pays for itself, and the monotone one — slope zero,
the output range — where it does not, both over `sigmoidEnclosure k`. `tanhRelaxation`
transports this whole.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The curvature relaxation where its bracket pays for itself, the monotone one elsewhere. -/
def sigmoidRelaxation (k : ℕ) : Relaxation 𝕋 :=
  Relaxation.tighter (sigmoidCurvatureRelaxation (sigmoidEnclosure k))
    (Relaxation.ofMonotone (sigmoidEnclosure k))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

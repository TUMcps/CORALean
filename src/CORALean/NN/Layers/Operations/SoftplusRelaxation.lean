module

public import CORALean.NN.Layers.Operations.SoftplusEnclosure
public import CORALean.NN.Layers.Operations.RelaxationOfMonotone

@[expose] public section

/-!
# The softplus relaxation

`Relaxation.ofMonotone` at `softplusEnclosure`: softplus is monotone for a positive sharpness.
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

/-- The slope-zero relaxation at that enclosure. -/
def softplusRelaxation (β : 𝕋) (k nl kl : ℕ) : Relaxation 𝕋 :=
  Relaxation.ofMonotone (softplusEnclosure β k nl kl)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

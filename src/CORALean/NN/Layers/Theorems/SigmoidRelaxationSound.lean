module

public import CORALean.NN.Layers.Operations.SigmoidRelaxation
public import CORALean.NN.Layers.Theorems.OfMonotoneSound
public import CORALean.NN.Layers.Theorems.SigmoidCurvatureRelaxationSound
public import CORALean.NN.Layers.Theorems.SigmoidEnclosureSound
public import CORALean.NN.Layers.Theorems.TighterSound

@[expose] public section

/-!
# The sigmoid relaxation is sound

Both halves are sound at the sound enclosure, so the tighter is too.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem sigmoidRelaxation_sound (k : ℕ) :
    (sigmoidRelaxation (𝕋 := 𝕋) k).Sound Real.sigmoid :=
  Relaxation.tighter_sound (sigmoidCurvatureRelaxation_sound (sigmoidEnclosure_sound k))
    (Relaxation.ofMonotone_sound Real.sigmoid_mono (sigmoidEnclosure_sound k))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

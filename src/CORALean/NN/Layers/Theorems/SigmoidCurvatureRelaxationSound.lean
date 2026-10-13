import CORALean.NN.Layers.Operations.SigmoidCurvatureRelaxation
import CORALean.NN.Layers.Theorems.Real.HasDerivAtSigmoid
import CORALean.NN.Layers.Theorems.LeSigmoidDerivHi
import CORALean.NN.Layers.Theorems.OfDerivSound
import CORALean.NN.Layers.Theorems.SigmoidDerivLoLe

/-!
# The sigmoid's curvature relaxation is sound

`Relaxation.ofDeriv_sound` at the bracket's two bounds, the clamped slope landing in the
bracket by `maximum`/`minimum`, both exact.
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

theorem sigmoidCurvatureRelaxation_sound {E : Enclosure 𝕋} (hE : E.Sound Real.sigmoid) :
    (sigmoidCurvatureRelaxation E).Sound Real.sigmoid :=
  Relaxation.ofDeriv_sound Real.sigmoidDeriv Real.hasDerivAt_sigmoid hE
    (sigmoidDerivLo_le hE) (le_sigmoidDerivHi hE) fun l u h => by
      refine ⟨by rw [sigmoidSlope, toReal_maximum]; exact le_max_left _ _, ?_⟩
      rw [sigmoidSlope, toReal_maximum, toReal_minimum]
      exact max_le (le_trans (sigmoidDerivLo_le hE l u (toReal l) le_rfl h)
        (le_sigmoidDerivHi hE l u (toReal l) le_rfl h)) (min_le_left _ _)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.NN.Layers.Operations.Basic
public import CORALean.NN.Layers.Theorems.Real.HasDerivAtSigmoid
public import CORALean.NN.Layers.Theorems.LeSigmoidDerivHi
public import CORALean.NN.Layers.Theorems.OfDerivEncloses
public import CORALean.NN.Layers.Theorems.SigmoidDerivLoLe
public import CORALean.NN.Layers.Operations.SigmoidRelaxation
public import CORALean.NN.Layers.Theorems.TighterEncloses
public import CORALean.NN.Layers.Theorems.OfMonotoneEncloses
public import CORALean.NN.Layers.Theorems.SigmoidEnclosureEncloses

@[expose] public section

/-!
# The sigmoid relaxation is sound

Both halves are sound at the sound enclosure, so the tighter one is too. The curvature half is
`aux_sigmoidCurvatureRelaxation_encloses`: `Relaxation.ofDeriv_encloses` at the bracket's two
bounds, the clamped slope landing in the bracket by `maximum`/`minimum`, both exact.

## Inputs
* `k` – sampling depth of the enclosure

## Hypotheses
* none

## Conclusion
* the sigmoid relaxation is sound for the sigmoid
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

private theorem aux_sigmoidCurvatureRelaxation_encloses {E : Enclosure 𝕋}
    (hE : E.Encloses Real.sigmoid) :
    (sigmoidCurvatureRelaxation E).Encloses Real.sigmoid :=
  Relaxation.ofDeriv_encloses Real.sigmoidDeriv Real.hasDerivAt_sigmoid hE
    (sigmoidDerivLo_le hE) (le_sigmoidDerivHi hE) fun l u h => by
      refine ⟨by rw [sigmoidSlope, toReal_maximum]; exact le_max_left _ _, ?_⟩
      rw [sigmoidSlope, toReal_maximum, toReal_minimum]
      exact max_le (le_trans (sigmoidDerivLo_le hE l u (toReal l) le_rfl h)
        (le_sigmoidDerivHi hE l u (toReal l) le_rfl h)) (min_le_left _ _)


-- =======================================  MAIN THEOREM  ======================================= --

/-- Both halves are sound at the sound enclosure, so the tighter is too. -/
theorem sigmoidRelaxation_encloses (k : ℕ) :
    (sigmoidRelaxation (𝕋 := 𝕋) k).Encloses Real.sigmoid :=
  Relaxation.tighter_encloses
    (aux_sigmoidCurvatureRelaxation_encloses (sigmoidEnclosure_encloses k))
    (Relaxation.ofMonotone_encloses Real.sigmoid_mono (sigmoidEnclosure_encloses k))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

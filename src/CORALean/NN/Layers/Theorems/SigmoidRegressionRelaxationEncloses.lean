module

public import CORALean.NN.Layers.Operations.SigmoidRegressionRelaxation
public import CORALean.NN.Layers.Theorems.Real.HasDerivAtSigmoid
public import CORALean.NN.Layers.Theorems.LeSigmoidDerivHi
public import CORALean.NN.Layers.Theorems.OfDerivEncloses
public import CORALean.NN.Layers.Theorems.OfMonotoneEncloses
public import CORALean.NN.Layers.Theorems.SigmoidDerivLoLe
public import CORALean.NN.Layers.Theorems.SigmoidEnclosureEncloses
public import CORALean.NN.Layers.Theorems.TighterEncloses
public import CORALean.NN.Layers.Theorems.Real.SigmoidMono

@[expose] public section

/-!
# The sigmoid relaxation at the regression line is sound

The regression slope is a guess: clamped into the derivative bracket it satisfies the hypothesis
of `Relaxation.ofDeriv_encloses`, whatever the floats in `step_regressionSlope` came to. The error
of the relaxation is measured against the stored line, so the line CORA fits costs precision and
never soundness. The slope-zero half is sound by monotonicity, and the tighter of two is sound.

## Inputs
* `k` – reduction depth of the exponential

## Hypotheses
* none

## Conclusion
* the relaxation is sound for the sigmoid
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       12-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The derivative-bracket half: the clamped slope lies in the bracket. -/
private theorem aux_ofDeriv_encloses {E : Enclosure 𝕋} (hE : E.Encloses Real.sigmoid) :
    (Relaxation.ofDeriv E (sigmoidDerivLo E) (sigmoidDerivHi E)
      (step_sigmoidRegressionSlope E)).Encloses Real.sigmoid :=
  Relaxation.ofDeriv_encloses Real.sigmoidDeriv Real.hasDerivAt_sigmoid hE
    (sigmoidDerivLo_le hE) (le_sigmoidDerivHi hE) fun l u h => by
      refine ⟨by rw [step_sigmoidRegressionSlope, toReal_maximum]; exact le_max_left _ _, ?_⟩
      rw [step_sigmoidRegressionSlope, toReal_maximum, toReal_minimum]
      exact max_le (le_trans (sigmoidDerivLo_le hE l u (toReal l) le_rfl h)
        (le_sigmoidDerivHi hE l u (toReal l) le_rfl h)) (min_le_left _ _)


-- =======================================  MAIN THEOREM  ======================================= --

theorem sigmoidRegressionRelaxation_encloses (k : ℕ) :
    (sigmoidRegressionRelaxation (𝕋 := 𝕋) k).Encloses Real.sigmoid :=
  Relaxation.tighter_encloses (aux_ofDeriv_encloses (sigmoidEnclosure_encloses k))
    (Relaxation.ofMonotone_encloses Real.sigmoid_mono (sigmoidEnclosure_encloses k))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.NN.Layers.Operations.SignRelaxation
public import CORALean.NN.Layers.Theorems.SignEnclosureEncloses
public import CORALean.NN.Layers.Theorems.OfMonotoneEncloses

@[expose] public section

/-!
# The sign relaxation is sound

The real sign is monotone and `signEnclosure` brackets it, so `Relaxation.ofMonotone_encloses`
applies: on every box the sign lies within the error of the offset.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* the relaxation is sound for the sign
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The real sign does not fall. -/
private theorem aux_sign_monotone :
    Monotone Real.sign := by
  intro a b hab
  unfold Real.sign
  split_ifs <;> linarith


-- =======================================  MAIN THEOREM  ======================================= --

theorem signRelaxation_encloses :
    (signRelaxation (𝕋 := 𝕋)).Encloses Real.sign := by
  exact Relaxation.ofMonotone_encloses aux_sign_monotone signEnclosure_encloses

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

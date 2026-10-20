module

public import CORALean.NN.Layers.Operations.ExpRelaxation
public import CORALean.NN.Layers.Theorems.OfMonotoneSoundWhere

@[expose] public section

/-!
# The exponential relaxation is sound

Where the right end is at most `2ᵏ/2`: `expDown` bounds `exp` from below everywhere and
`le_expUp` from above there, and `exp` is monotone.

## Inputs
* `k` – reduction depth

## Hypotheses
* none

## Conclusion
* the relaxation is sound for the exponential where the upper end is in range
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem expRelaxation_sound (k : ℕ) :
    (expRelaxation (𝕋 := 𝕋) k).SoundWhere Real.exp fun _ u => toReal u ≤ 2 ^ k / 2 :=
  Relaxation.ofMonotone_soundWhere (fun _ _ _ => Real.exp_monotone) (fun l _ _ => expDown_le k l)
    fun _ u hP => le_expUp k u hP

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

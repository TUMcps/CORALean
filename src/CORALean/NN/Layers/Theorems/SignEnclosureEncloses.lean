module

public import CORALean.NN.Layers.Operations.SignEnclosure
public import Mathlib.Data.Real.Sign

@[expose] public section

/-!
# The sign enclosure is sound

Each end decides by a comparison that is sound for it: a `true` `ltStrict` proves the value of
that sign, a `true` `le` proves it on one side of zero, and the fallback `-1` or `1` bounds every
sign.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* the enclosure brackets the real sign at every stored value
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem signEnclosure_encloses : -- --- CONCL ---
    (signEnclosure (𝕋 := 𝕋)).Encloses Real.sign := by -- --- PROOF ---
  -- the real sign is `-1`, `0` or `1` by the two strict comparisons with zero
  refine ⟨fun a => ?_, fun a => ?_⟩
  · show toReal (step_signDown a) ≤ _
    unfold step_signDown
    split_ifs with h1 h2
    · rw [toReal_one, Real.sign_of_pos (by simpa [toReal_zero] using toReal_lt_of_ltStrict h1)]
    · have h := toReal_le_of_le h2
      rw [toReal_zero] at h ⊢
      unfold Real.sign; split_ifs <;> linarith
    · rw [toReal_neg, toReal_one]; unfold Real.sign; split_ifs <;> norm_num
  · show _ ≤ toReal (step_signUp a)
    unfold step_signUp
    split_ifs with h1 h2
    · rw [toReal_neg, toReal_one,
        Real.sign_of_neg (by simpa [toReal_zero] using toReal_lt_of_ltStrict h1)]
    · have h := toReal_le_of_le h2
      rw [toReal_zero] at h ⊢
      unfold Real.sign; split_ifs <;> linarith
    · rw [toReal_one]; unfold Real.sign; split_ifs <;> norm_num

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.NN.Operations.Basic
public import CORALean.NN.Definitions.Basic

@[expose] public section

/-!
# `reluDerEnclosure` encloses the derivative of ReLU
Case split on the two certificates: a certified positive lower bound makes every point of the
box positive, a certified nonpositive upper bound makes every one nonpositive.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* the enclosure contains the derivative of ReLU
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem reluDerEnclosure_encloses : -- --- CONCL ---
    EnclosesScalar (reluDerEnclosure (𝕋 := 𝕋))
      (fun x => if 0 < x then 1 else 0) := by -- --- PROOF ---
  intro I x hl hu
  constructor
  · by_cases h : ltStrict zero I.inf = true
    · have h0 := toReal_lt_of_ltStrict h
      rw [toReal_zero] at h0
      simp [reluDerEnclosure, h, toReal_one, lt_of_lt_of_le h0 hl]
    · simp only [reluDerEnclosure, h, Bool.false_eq_true, if_false, toReal_zero]
      split_ifs <;> norm_num
  · by_cases h : le I.sup zero = true
    · have h0 := toReal_le_of_le h
      rw [toReal_zero] at h0
      simp [reluDerEnclosure, h, toReal_zero, not_lt.mpr (hu.trans h0)]
    · simp only [reluDerEnclosure, h, Bool.false_eq_true, if_false, toReal_one]
      split_ifs <;> norm_num

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

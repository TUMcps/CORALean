module

public import CORALean.Global.Float.SqrtDownCora

@[expose] public section

/-!
# `sqrtDownCora` is below the real root

The format's own lower root by the law `SoundFloatArithmetic.sqrtDownOverride_le` states for it,
at `r = √a` (whose square is the clamped radicand), otherwise `sqrtDown_le`.

## Inputs
* `p` – Newton steps
* `a` – radicand

## Hypotheses
* none

## Conclusion
* the root from below is at most the real square root
-/

-- Authors:       Claude Sonnet 5.5, Claude Opus 5.5
-- Written:       21-November-2026
-- Last update:   23-November-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The root from below is under the real one, whatever the fuel. -/
theorem sqrtDownCora_le (p : ℕ) (a : 𝕋) : -- --- CONCL ---
    toReal (sqrtDownCora p a) ≤ Real.sqrt (toReal a) := by -- --- PROOF ---
  unfold sqrtDownCora
  split
  · rename_i f hf
    refine SoundFloatArithmetic.sqrtDownOverride_le hf p a _ (Real.sqrt_nonneg _) ?_
    rcases le_total 0 (toReal a) with h | h
    · rw [Real.mul_self_sqrt h]; exact max_le le_rfl h
    · rw [Real.sqrt_eq_zero_of_nonpos h]; simpa using h
  · exact sqrtDown_le p a

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

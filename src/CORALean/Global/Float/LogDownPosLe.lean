module

public import CORALean.Global.Float.LogDownPos

@[expose] public section

/-!
# `logDownPos` is below the real logarithm

The format's own `log` is exact (`SoundFloatArithmetic.elemOverride_std`); otherwise
`1 / a ≤ (1 / a)` rounded up, `log` grows and `le_logUp` bounds it, so the negation is below
`-(log(1 / a)) = log a`.

## Inputs
* `n` – precision of the exponential
* `k` – number of bisection steps
* `a` – float argument

## Hypotheses
* `ha` – the argument is positive

## Conclusion
* the logarithm from below is at most the real one
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem logDownPos_le (n k : ℕ) (a : 𝕋) (ha : 0 < toReal a) : -- --- CONCL ---
    toReal (logDownPos n k a) ≤ Real.log (toReal a) := by -- --- PROOF ---
  unfold logDownPos
  split
  · next e he => exact ((SoundFloatArithmetic.elemOverride_std e he).2.2.2.1 a ha).le
  · have hq := div_le_divUp one a ha
    rw [toReal_one] at hq
    have hq0 : 0 < 1 / toReal a := by positivity
    have hlog := le_logUp n k (divUp one a) (lt_of_lt_of_le hq0 hq)
    have hmono := Real.log_le_log hq0 hq
    rw [one_div, Real.log_inv] at hmono
    rw [toReal_neg]
    linarith

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

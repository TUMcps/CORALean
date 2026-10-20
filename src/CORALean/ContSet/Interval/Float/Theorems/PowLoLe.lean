module

public import CORALean.ContSet.Interval.Float.Operations.PowLo

@[expose] public section

/-!
# `Interval.powLo` is a lower bound on the power

Even: `a ^ k = |a| ^ k`. Odd: `le zero a` makes `a` nonnegative (`powDown_le`); otherwise
`a ^ k ≥ (-|a|) ^ k = -|a| ^ k` by monotonicity of an odd power.

## Inputs
* `a` – end point
* `k` – exponent

## Hypotheses
* none

## Conclusion
* the lower bound is below the real power of the end point
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.powLo_le (a : 𝕋) (k : ℕ) :
    toReal (Interval.powLo a k) ≤ toReal a ^ k := by -- --- PROOF ---
  have habs : toReal (absolute a) = |toReal a| := toReal_absolute a
  unfold Interval.powLo
  by_cases he : k % 2 = 0
  · -- even: the power of the absolute value
    rw [if_pos he]
    have hev : Even k := Nat.even_iff.mpr he
    rw [← hev.pow_abs]
    exact powDown_le (by rw [habs]; exact abs_nonneg _) habs.le k
  · -- odd: by the certified sign of `a`
    rw [if_neg he]
    have ho : Odd k := Nat.odd_iff.mpr (by omega)
    by_cases h0 : le zero a = true
    · -- `a ≥ 0`: `powDown a` itself
      rw [if_pos h0]
      have := toReal_le_of_le h0
      rw [toReal_zero] at this
      exact powDown_le this le_rfl k
    · -- otherwise `a ^ k ≥ (-|a|) ^ k = -|a| ^ k`
      rw [if_neg h0]
      have hu := le_powUp (B := absolute a) (x := |toReal a|) (abs_nonneg _) habs.ge k
      rw [toReal_neg]
      have h2 : (-|toReal a|) ^ k ≤ toReal a ^ k :=
        ho.strictMono_pow.monotone (neg_abs_le _)
      rw [ho.neg_pow] at h2
      linarith

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

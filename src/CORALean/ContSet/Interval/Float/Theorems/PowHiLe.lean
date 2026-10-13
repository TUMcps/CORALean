module

public import CORALean.ContSet.Interval.Float.Operations.PowHi

@[expose] public section

/-!
# `Interval.powHi` is an upper bound on the power

Even: `a ^ k = |a| ^ k`. Odd: `le zero a` makes `a` nonnegative (`le_powUp`), `le a zero` makes
`a ^ k = -|a| ^ k` (`powDown_le`); otherwise `a ^ k ≤ |a| ^ k` by monotonicity of an odd power.
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

theorem Interval.le_powHi (a : 𝕋) (k : ℕ) :
    toReal a ^ k ≤ toReal (Interval.powHi a k) := by -- --- PROOF ---
  have habs : toReal (absolute a) = |toReal a| := toReal_absolute a
  unfold Interval.powHi
  by_cases he : k % 2 = 0
  · -- even: the power of the absolute value
    rw [if_pos he]
    have hev : Even k := Nat.even_iff.mpr he
    rw [← hev.pow_abs]
    exact le_powUp (abs_nonneg _) habs.ge k
  · -- odd: by the certified sign of `a`
    rw [if_neg he]
    have ho : Odd k := Nat.odd_iff.mpr (by omega)
    by_cases h0 : le zero a = true
    · -- `a ≥ 0`: `powUp a` itself
      rw [if_pos h0]
      have := toReal_le_of_le h0
      rw [toReal_zero] at this
      exact le_powUp this le_rfl k
    · -- sign not certified nonnegative
      rw [if_neg h0]
      by_cases h1 : le a zero = true
      · -- `a ≤ 0`: `a ^ k = -|a| ^ k`, bounded above by `powDown`
        rw [if_pos h1]
        have hr := toReal_le_of_le h1
        rw [toReal_zero] at hr
        have hb := powDown_le (B := absolute a) (x := |toReal a|) (by rw [habs]; exact abs_nonneg _)
          habs.le k
        rw [toReal_neg]
        have : toReal a ^ k = -(|toReal a| ^ k) := by
          rw [← ho.neg_pow, abs_of_nonpos hr, neg_neg]
        linarith
      · -- no sign certified: `a ^ k ≤ |a| ^ k`
        rw [if_neg h1]
        refine le_trans ?_ (le_powUp (abs_nonneg _) habs.ge k)
        exact ho.strictMono_pow.monotone (le_abs_self _)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

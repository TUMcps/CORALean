import CORALean.ContSet.Interval.Float.Theorems.PowHiLe
import CORALean.ContSet.Interval.Float.Theorems.PowLoLe
import CORALean.ContSet.Interval.Float.Operations.Power
import CORALean.ContSet.Interval.Real.Theorems.PowerBetween

/-!
# `Interval.power` encloses the powers of the points of the box

For `x` in the box, `x ^ k` lies between the bounds: the upper one by `le_powHi` at the corner
`pow_between` names; the lower one is `0` for an uncertified even power (always valid), else the
minimum of the two `powLo` values, under `min (a ^ k) (b ^ k) ≤ x ^ k`, the real scalar fact, which
applies because the `le` certificates rule out the case `a < 0 < b`.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.power_outer (I : Interval (Vec 𝕋 n)) (k : ℕ) :
    (fun x i => x i ^ k) '' I.construct ⊆ (I.power k).construct := by -- --- PROOF ---
  rintro _ ⟨x, hx, rfl⟩ i
  have h₁ : toReal (I.inf i) ≤ x i := (hx i).1
  have h₂ : x i ≤ toReal (I.sup i) := (hx i).2
  -- the real scalar fact, at the stored corners
  have hb := Real.Interval.pow_between k h₁ h₂
  show toReal ((I.power k).inf i) ≤ x i ^ k ∧ x i ^ k ≤ toReal ((I.power k).sup i)
  refine ⟨?_, ?_⟩
  · show toReal (if k % 2 = 0 ∧ k ≠ 0 ∧ (le zero (I.inf i) || le (I.sup i) zero) = false
        then zero else minimum (Interval.powLo (I.inf i) k) (Interval.powLo (I.sup i) k)) ≤ _
    by_cases hc : k % 2 = 0 ∧ k ≠ 0 ∧ (le zero (I.inf i) || le (I.sup i) zero) = false
    · -- uncertified even power: `0` is a lower bound
      rw [if_pos hc, toReal_zero]
      exact (Nat.even_iff.mpr hc.1).pow_nonneg _
    · -- one side of `0` certified (or an odd power): the real minimum, not the special case
      rw [if_neg hc, toReal_minimum]
      have hns : ¬ (k % 2 = 0 ∧ k ≠ 0 ∧ toReal (I.inf i) < 0 ∧ 0 < toReal (I.sup i)) := by
        rintro ⟨h0, h1, ha, hbb⟩
        apply hc
        refine ⟨h0, h1, ?_⟩
        by_contra hd
        rw [Bool.not_eq_false, Bool.or_eq_true] at hd
        rcases hd with hl | hl
        · have := toReal_le_of_le hl; rw [toReal_zero] at this; linarith
        · have := toReal_le_of_le hl; rw [toReal_zero] at this; linarith
      rw [if_neg hns] at hb
      exact le_trans (min_le_min (Interval.powLo_le _ k) (Interval.powLo_le _ k)) hb.1
  · -- the upper bound is the maximum of the two rounded-up corner powers
    show x i ^ k ≤ toReal (maximum (Interval.powHi (I.inf i) k) (Interval.powHi (I.sup i) k))
    rw [toReal_maximum]
    exact le_trans hb.2 (max_le_max (Interval.le_powHi _ k) (Interval.le_powHi _ k))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

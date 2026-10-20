module

public import CORALean.ContSet.Taylm.Float.Operations.InvCoef
public import Mathlib.Analysis.Calculus.Deriv.ZPow
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

@[expose] public section

/-!
# The coefficients of `1/x` contain the Taylor coefficient

`iteratedDeriv k (1/·) c / k! = (-1)ᵏ c⁻⁽ᵏ⁺¹⁾`, between the two ends of `invCoef`: the magnitude
`(1/|c|)ᵏ⁺¹` lies between the directed powers of the rounded reciprocal, and the sign is
read off where `ltStrict` certifies it, an uncertified sign being covered by the symmetric
interval.

## Inputs
* `c` – center
* `k` – coefficient index

## Hypotheses
* `hc` – the center is nonzero

## Conclusion
* the true reciprocal coefficient lies in the enclosure
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.invCoef_mem (c : 𝕋) (hc : toReal c ≠ 0) (k : ℕ) : -- --- CONCL ---
    toReal (Taylm.invCoef c k).inf ≤
        iteratedDeriv k (fun x : ℝ => x⁻¹) (toReal c) / (k.factorial : ℝ) ∧
      iteratedDeriv k (fun x : ℝ => x⁻¹) (toReal c) / (k.factorial : ℝ) ≤
        toReal (Taylm.invCoef c k).sup := by -- --- PROOF ---
  -- the coefficient as a signed power
  have hd : iteratedDeriv k (fun x : ℝ => x⁻¹) (toReal c) / (k.factorial : ℝ) =
      (-1) ^ k * (toReal c)⁻¹ ^ (k + 1) := by
    rw [iteratedDeriv_eq_iterate, show (fun x : ℝ => x⁻¹) = Inv.inv from rfl, iter_deriv_inv,
      show (-1 - (k : ℤ)) = -((k + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast,
      inv_pow]
    have : (k.factorial : ℝ) ≠ 0 := by positivity
    field_simp
  -- the magnitude of `c`, its reciprocal's roundings and powers
  have hs : toReal (maximum c (neg c)) = |toReal c| := by
    rw [toReal_maximum, toReal_neg]; exact (abs_eq_max_neg).symm
  have hspos : 0 < |toReal c| := abs_pos.mpr hc
  have hdiv1 := div_le_divUp (one : 𝕋) (maximum c (neg c)) (by rw [hs]; exact hspos)
  have hdiv2 := divDown_le_div (one : 𝕋) (maximum c (neg c)) (by rw [hs]; exact hspos)
  rw [toReal_one, hs] at hdiv1 hdiv2
  have hw0 : (0 : ℝ) ≤ toReal (maximum zero (divDown one (maximum c (neg c)))) := by
    rw [toReal_maximum, toReal_zero]; exact le_max_left _ _
  have hwl : toReal (maximum zero (divDown one (maximum c (neg c)))) ≤ 1 / |toReal c| := by
    rw [toReal_maximum, toReal_zero]; exact max_le (by positivity) hdiv2
  have hpl := powDown_le hw0 hwl (k + 1)
  have hph := le_powUp (by positivity : (0 : ℝ) ≤ 1 / |toReal c|) hdiv1 (k + 1)
  -- the magnitude of the coefficient
  have hmag : |(toReal c)⁻¹ ^ (k + 1)| = (1 / |toReal c|) ^ (k + 1) := by
    rw [abs_pow, abs_inv, one_div]
  unfold Taylm.invCoef
  simp only []
  by_cases hp : ltStrict zero c = true
  · -- a certified positive center
    have h0 : 0 < toReal c := by simpa [toReal_zero] using toReal_lt_of_ltStrict hp
    rw [abs_of_pos h0] at hpl hph
    rw [if_pos hp, hd]
    have hcc : (toReal c)⁻¹ ^ (k + 1) = (1 / toReal c) ^ (k + 1) := by rw [one_div]
    split_ifs with hk
    · rw [(Nat.even_iff.mpr hk).neg_one_pow, one_mul, hcc]
      exact ⟨hpl, hph⟩
    · rw [(Nat.odd_iff.mpr (by omega)).neg_one_pow, hcc, toReal_neg, toReal_neg]
      constructor <;> linarith
  · by_cases hn : ltStrict c zero = true
    · -- a certified negative center
      have h0 : toReal c < 0 := by simpa [toReal_zero] using toReal_lt_of_ltStrict hn
      rw [abs_of_neg h0] at hpl hph
      rw [if_neg hp, if_pos hn, hd, toReal_neg, toReal_neg]
      -- `(-1)ᵏ c⁻⁽ᵏ⁺¹⁾` is `-(1/|c|)ᵏ⁺¹`, whichever the parity
      have key : ∀ a : ℝ, (-1 : ℝ) ^ k * (-a) ^ (k + 1) = -a ^ (k + 1) := by
        intro a
        rw [neg_pow a (k + 1), pow_succ (-1 : ℝ) k]
        have : ((-1 : ℝ) ^ k) * ((-1 : ℝ) ^ k) = 1 := by rw [← mul_pow]; simp
        linear_combination (-(a ^ (k + 1))) * this
      have hneg : (-1 : ℝ) ^ k * (toReal c)⁻¹ ^ (k + 1) = -(1 / -toReal c) ^ (k + 1) := by
        rw [show (toReal c)⁻¹ = -(-toReal c)⁻¹ by rw [inv_neg, neg_neg], key, one_div]
      rw [hneg]
      constructor <;> linarith
    · -- an uncertified sign: the symmetric interval
      rw [if_neg hp, if_neg hn, hd, toReal_neg]
      have h1 : |(-1 : ℝ) ^ k * (toReal c)⁻¹ ^ (k + 1)| ≤
          toReal (powUp (divUp one (maximum c (neg c))) (k + 1)) := by
        rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, hmag]
        exact hph
      exact abs_le.mp h1

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

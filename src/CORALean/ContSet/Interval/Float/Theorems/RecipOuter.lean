module

public import CORALean.ContSet.Interval.Float.Operations.Recip
public import CORALean.ContSet.Interval.Real.Theorems.InvBetween

@[expose] public section

/-!
# `Interval.recip` over-approximates the reciprocal image, over a floating-point scalar

Per coordinate the real reciprocal brackets the point's reciprocal (`aux_inv_between`), and the
directed divisions bracket the real reciprocals: `divUp one a` is above `1/a` and `divDown one b`
below `1/b`, for positive `a` and `b`. A negative coordinate is negated first. The box is
assumed to avoid `0`, certified by `ltStrict` as the float operations are.

## Inputs
* `J` – second interval box

## Hypotheses
* `hJ` – no coordinate of `J` contains zero

## Conclusion
* every coordinatewise reciprocal of a box point lies in the result box
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.recip_outer (J : Interval (Vec 𝕋 n))
    (hJ : ∀ i, ltStrict zero (J.inf i) = true ∨ ltStrict (J.sup i) zero = true) :
    (fun y i => (y i)⁻¹) '' J.construct ⊆ J.recip.construct := by -- --- PROOF ---
  rintro _ ⟨y, hy, rfl⟩ i
  have h₁ : toReal (J.inf i) ≤ y i := (hy i).1
  have h₂ : y i ≤ toReal (J.sup i) := (hy i).2
  show toReal (J.recip.inf i) ≤ (y i)⁻¹ ∧ (y i)⁻¹ ≤ toReal (J.recip.sup i)
  unfold Interval.recip
  -- a coordinate above `0`: both bounds positive
  by_cases hp : ltStrict zero (J.inf i) = true
  · have ha : 0 < toReal (J.inf i) := by simpa [toReal_zero] using toReal_lt_of_ltStrict hp
    have hb : 0 < toReal (J.sup i) := ha.trans_le (h₁.trans h₂)
    obtain ⟨hl, hu⟩ := Real.Interval.inv_between (Or.inl ha) h₁ h₂
    simp only [hp, if_true]
    refine ⟨le_trans ?_ hl, le_trans hu ?_⟩
    · have := divDown_le_div (one : 𝕋) (J.sup i) hb
      simpa [toReal_one] using this
    · have := div_le_divUp (one : 𝕋) (J.inf i) ha
      simpa [toReal_one] using this
  -- otherwise the certificate says the coordinate is below `0`: negate and divide
  · have hn : ltStrict (J.sup i) zero = true := (hJ i).resolve_left hp
    have hb : toReal (J.sup i) < 0 := by simpa [toReal_zero] using toReal_lt_of_ltStrict hn
    have ha : toReal (J.inf i) < 0 := lt_of_le_of_lt (h₁.trans h₂) hb
    obtain ⟨hl, hu⟩ := Real.Interval.inv_between (Or.inr hb) h₁ h₂
    simp only [hp, if_false, Bool.false_eq_true, toReal_neg]
    have hnb : 0 < toReal (neg (J.sup i)) := by rw [toReal_neg]; linarith
    have hna : 0 < toReal (neg (J.inf i)) := by rw [toReal_neg]; linarith
    refine ⟨le_trans ?_ hl, le_trans hu ?_⟩
    · have := div_le_divUp (one : 𝕋) (neg (J.sup i)) hnb
      rw [toReal_one, toReal_neg, one_div, ← neg_inv] at this
      linarith
    · have := divDown_le_div (one : 𝕋) (neg (J.inf i)) hna
      rw [toReal_one, toReal_neg, one_div, ← neg_inv] at this
      linarith

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

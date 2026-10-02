import CORALean.ContSet.Interval.Float.Operations.Mrdivide

/-!
# `Interval.mrdivide` over-approximates division by a scalar, over a floating-point scalar

For positive `d` the quotient of an endpoint is bracketed by the directed division of the stored
one; for negative `d` the negated box over `-d` is the same quotient, with the endpoints swapped.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.mrdivide_outer (I : Interval (Vec 𝕋 n)) (d : 𝕋)
    (hd : ltStrict zero d = true ∨ ltStrict d zero = true) :
    (fun x i => x i / toReal d) '' I.construct ⊆ (I.mrdivide d).construct := by -- --- PROOF ---
  rintro _ ⟨x, hx, rfl⟩ i
  have h₁ : toReal (I.inf i) ≤ x i := (hx i).1
  have h₂ : x i ≤ toReal (I.sup i) := (hx i).2
  show toReal ((I.mrdivide d).inf i) ≤ x i / toReal d
    ∧ x i / toReal d ≤ toReal ((I.mrdivide d).sup i)
  unfold Interval.mrdivide
  -- a positive `d`: the endpoints keep their order
  by_cases hp : ltStrict zero d = true
  · have hpos : 0 < toReal d := by simpa [toReal_zero] using toReal_lt_of_ltStrict hp
    simp only [hp, if_true]
    exact ⟨le_trans (divDown_le_div _ _ hpos) (div_le_div_of_nonneg_right h₁ hpos.le),
      le_trans (div_le_div_of_nonneg_right h₂ hpos.le) (div_le_divUp _ _ hpos)⟩
  -- a negative `d`: negate the box and `d`, which swaps the endpoints
  · have hn : ltStrict d zero = true := (hd.resolve_left hp)
    have hneg : toReal d < 0 := by simpa [toReal_zero] using toReal_lt_of_ltStrict hn
    have hnd : 0 < toReal (neg d) := by rw [toReal_neg]; linarith
    simp only [hp, if_false, Bool.false_eq_true]
    refine ⟨le_trans (divDown_le_div _ _ hnd) ?_, le_trans ?_ (div_le_divUp _ _ hnd)⟩
    · rw [toReal_neg, toReal_neg, neg_div_neg_eq]
      exact div_le_div_of_nonpos_of_le hneg.le h₂
    · rw [toReal_neg, toReal_neg, neg_div_neg_eq]
      exact div_le_div_of_nonpos_of_le hneg.le h₁

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

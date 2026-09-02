import CORALean.Global.Float.Instances.Dyadic.Theorems.Rounding

/-!
# Division goes the way it says

The same fact as `Rounding`, `Int.ediv_mul_le`, applied one step earlier: the
quotient is rounded while it is still two integers, since afterwards it is a
rational nothing on the grid equals.

The whole content is that shifting the dividend left by `p` bits and lowering
the exponent by `p` is the identity on ℝ, so the only inequality left is between
an integer quotient and a real one. A positive divisor is what the direction
depends on — with a negative one the floor of the mantissa quotient is an upper
bound, not a lower — and `SoundFloatArithmetic` asks for exactly that.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float.Dyadic

variable {p : ℕ}

private theorem toReal_mk (m e : ℤ) : toReal (⟨m, e⟩ : Dyadic p) = (m : ℝ) * 2 ^ e := rfl

/-- The scale is positive, so the sign is the mantissa's. -/
private theorem mantissa_pos {b : Dyadic p} (hb : 0 < toReal b) : 0 < b.mantissa := by
  by_contra h
  have hc : ((b.mantissa : ℝ)) ≤ 0 := Int.cast_nonpos.mpr (not_lt.mp h)
  have hz := mul_le_mul_of_nonneg_right hc (le_of_lt (zpow_pos two_pos b.exponent))
  rw [zero_mul] at hz
  exact absurd hb (not_lt.mpr hz)

/-- The dividend's `p`-bit shift and the exponent's `-p` cancel, which is what
leaves an integer quotient facing a real one. -/
private theorem toReal_div_eq (a b : Dyadic p) (hb : (b.mantissa : ℝ) ≠ 0) :
    toReal a / toReal b
      = ((a.mantissa * 2 ^ p : ℤ) : ℝ) / ((b.mantissa : ℤ) : ℝ)
          * 2 ^ (a.exponent - b.exponent - (p : ℤ)) := by
  have h2 : (2 : ℝ) ≠ 0 := two_ne_zero
  have hea : ((2 : ℝ) ^ a.exponent) ≠ 0 := zpow_ne_zero _ h2
  have heb : ((2 : ℝ) ^ b.exponent) ≠ 0 := zpow_ne_zero _ h2
  have hpp : ((2 : ℝ) ^ p) ≠ 0 := pow_ne_zero _ h2
  rw [toReal, toReal, zpow_sub₀ h2, zpow_sub₀ h2, zpow_natCast]
  push_cast
  field_simp

theorem quotDown_le_div (a b : Dyadic p) (hb : 0 < toReal b) :
    toReal (quotDown a b) ≤ toReal a / toReal b := by
  have hm : 0 < b.mantissa := mantissa_pos hb
  have hmR : (0 : ℝ) < (b.mantissa : ℝ) := Int.cast_pos.mpr hm
  rw [toReal_div_eq a b (ne_of_gt hmR), quotDown, toReal_mk]
  refine mul_le_mul_of_nonneg_right ?_ (le_of_lt (zpow_pos two_pos _))
  rw [le_div_iff₀ hmR]
  exact_mod_cast Int.ediv_mul_le (a.mantissa * 2 ^ p) (ne_of_gt hm)

theorem le_quotUp (a b : Dyadic p) (hb : 0 < toReal b) :
    toReal a / toReal b ≤ toReal (quotUp a b) := by
  have hm : 0 < b.mantissa := mantissa_pos hb
  have hmR : (0 : ℝ) < (b.mantissa : ℝ) := Int.cast_pos.mpr hm
  rw [toReal_div_eq a b (ne_of_gt hmR), quotUp, toReal_mk]
  refine mul_le_mul_of_nonneg_right ?_ (le_of_lt (zpow_pos two_pos _))
  rw [div_le_iff₀ hmR]
  have h := Int.ediv_mul_le (-(a.mantissa * 2 ^ p)) (ne_of_gt hm)
  have h' : a.mantissa * 2 ^ p
      ≤ -(-(a.mantissa * 2 ^ p) / b.mantissa) * b.mantissa := by
    rw [neg_mul]
    linarith
  exact_mod_cast h'

theorem divDown_le_div (a b : Dyadic p) (hb : 0 < toReal b) :
    toReal (divDown a b) ≤ toReal a / toReal b :=
  le_trans (roundDown_le _) (quotDown_le_div a b hb)

theorem le_divUp (a b : Dyadic p) (hb : 0 < toReal b) :
    toReal a / toReal b ≤ toReal (divUp a b) :=
  le_trans (le_quotUp a b hb) (le_roundUp _)

end CORALean.Float.Dyadic

import CORALean.Arithmetic.Float.Instances.Dyadic.API

/-!
# The exact step loses nothing

`exactAdd` and `exactMul` agree with ℝ on the nose. All the approximation in
`Dyadic` therefore sits in the rounding step, and nowhere else.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Arithmetic.Float.Dyadic

variable {p : ℕ}

/-- Re-associating an alignment: a mantissa scaled by `2 ^ (f - e)` and read at
exponent `e` is the same number read at exponent `f`. -/
private theorem two_zpow_align {e f : ℤ} (h : e ≤ f) :
    (2 : ℝ) ^ (f - e).toNat * 2 ^ e = 2 ^ f := by
  rw [← zpow_natCast (2 : ℝ) (f - e).toNat, Int.toNat_of_nonneg (sub_nonneg.mpr h),
    ← zpow_add₀ (two_ne_zero), sub_add_cancel]

/-- Any exponent, since a zero mantissa reads as zero at every scale. -/
theorem toReal_mk_zero (e : ℤ) : toReal (⟨0, e⟩ : Dyadic p) = 0 := by
  show ((0 : ℤ) : ℝ) * 2 ^ e = 0
  rw [Int.cast_zero, zero_mul]

/-- A dyadic read at any exponent at or below its own. -/
theorem toReal_align (d : Dyadic p) {e : ℤ} (h : e ≤ d.exponent) :
    toReal d = ((d.mantissa * 2 ^ (d.exponent - e).toNat : ℤ) : ℝ) * 2 ^ e := by
  rw [toReal]
  push_cast
  rw [mul_assoc, two_zpow_align h]

theorem toReal_neg (d : Dyadic p) : toReal (neg d) = -toReal d := by
  rw [toReal, toReal, neg, Int.cast_neg, neg_mul]

theorem toReal_half (a : Dyadic p) : toReal (half a) = toReal a / 2 := by
  rw [toReal, toReal, half, zpow_sub₀ (two_ne_zero), zpow_one]
  ring

theorem toReal_exactAdd (a b : Dyadic p) :
    toReal (exactAdd a b) = toReal a + toReal b := by
  rw [toReal, toReal, toReal, exactAdd]
  push_cast
  rw [add_mul, mul_assoc, mul_assoc, two_zpow_align (min_le_left a.exponent b.exponent),
    two_zpow_align (min_le_right a.exponent b.exponent)]

theorem toReal_exactMul (a b : Dyadic p) :
    toReal (exactMul a b) = toReal a * toReal b := by
  rw [toReal, toReal, toReal, exactMul, Int.cast_mul, zpow_add₀ (two_ne_zero)]
  ring

end CORALean.Arithmetic.Float.Dyadic

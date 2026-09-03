import CORALean.Global.Float.Instances.Dyadic.Operations

/-!
# Rounding goes the way it says

Both bounds come from one fact, `Int.ediv_mul_le`: floor division never
overshoots. `roundUp` is that fact applied to the negated mantissa, which is
what makes the ceiling case free.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float.Dyadic

variable {p : ℕ}

/-- Dropping `k` bits and raising the exponent by `k` leaves only mantissas to compare. -/
private theorem toReal_shift (m e : ℤ) (k : ℕ) :
    toReal (⟨m, e + k⟩ : Dyadic p) = ((m * 2 ^ k : ℤ) : ℝ) * 2 ^ e := by
  rw [toReal_def, zpow_add₀ (two_ne_zero), zpow_natCast]
  push_cast
  ring

theorem roundDown_le (d : Dyadic p) : toReal (roundDown d) ≤ toReal d := by
  rw [roundDown, toReal_shift, toReal_def]
  exact mul_le_mul_of_nonneg_right
    (Int.cast_le.mpr (Int.ediv_mul_le _ (pow_ne_zero _ two_ne_zero)))
    (le_of_lt (zpow_pos two_pos _))

theorem le_roundUp (d : Dyadic p) : toReal d ≤ toReal (roundUp d) := by
  have h : d.mantissa ≤ -(-d.mantissa / 2 ^ d.shift) * 2 ^ d.shift := by
    rw [neg_mul, le_neg]
    exact Int.ediv_mul_le _ (pow_ne_zero _ two_ne_zero)
  rw [roundUp, toReal_shift, toReal_def]
  exact mul_le_mul_of_nonneg_right (Int.cast_le.mpr h) (le_of_lt (zpow_pos two_pos _))

end CORALean.Float.Dyadic

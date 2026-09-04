import CORALean.Global.Float.Instances.Dyadic.Theorems.Exact

/-!
# Comparison agrees with ℝ

Aligned to the common exponent, both numbers are a mantissa times one positive
scale, so comparing them is comparing integers. `minimum` and `maximum` are then
exact, which is what lets them absorb a sign without widening anything.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   04-September-2026
-- Last revision: ---

namespace CORALean.Float.Dyadic

variable {p : ℕ}

private theorem aux_le_iff (a b : Dyadic p) : le a b = true ↔ toReal a ≤ toReal b := by
  rw [le, decide_eq_true_eq, toReal_align a (min_le_left a.exponent b.exponent),
    toReal_align b (min_le_right a.exponent b.exponent)]
  exact ⟨fun h => mul_le_mul_of_nonneg_right (Int.cast_le.mpr h) (le_of_lt (zpow_pos two_pos _)),
         fun h => Int.cast_le.mp (le_of_mul_le_mul_right h (zpow_pos two_pos _))⟩

theorem toReal_minimum (a b : Dyadic p) :
    toReal (minimum a b) = min (toReal a) (toReal b) := by
  by_cases h : le a b = true
  · rw [minimum, if_pos h, min_eq_left ((aux_le_iff a b).mp h)]
  · rw [minimum, if_neg h, min_eq_right (not_le.mp (h ∘ (aux_le_iff a b).mpr)).le]

theorem toReal_maximum (a b : Dyadic p) :
    toReal (maximum a b) = max (toReal a) (toReal b) := by
  by_cases h : le a b = true
  · rw [maximum, if_pos h, max_eq_right ((aux_le_iff a b).mp h)]
  · rw [maximum, if_neg h, max_eq_left (not_le.mp (h ∘ (aux_le_iff a b).mpr)).le]

/-- The direction `SoundFloatArithmetic` asks for; the converse holds too
(`aux_le_iff`), but nothing here needs it. -/
theorem toReal_le_of_le {a b : Dyadic p} (h : le a b = true) : toReal a ≤ toReal b :=
  (aux_le_iff a b).mp h

end CORALean.Float.Dyadic

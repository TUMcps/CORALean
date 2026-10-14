module

public import CORALean.Global.Float.Instances.Dyadic.Dyadic
public import CORALean.Global.Float.Instances.Dyadic.Operations.Basic
public import CORALean.Global.Float.Instances.Dyadic.Operations.ToRat
public import CORALean.Global.Float.Instances.Dyadic.Theorems.LeIff
public import Mathlib.Algebra.Ring.CharZero

@[expose] public section

/-!
# `Global/Float/Instances/Dyadic/Theorems`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean.Float


-- ===================================  `Dyadic.cast_toRat`  ==================================== --
-- Authors:       Claude Opus 5.5
-- Written:       30-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `toReal` already takes its power of two through ℚ, so the two agree by casting
the product: nothing is rounded on either side. -/
theorem Dyadic.cast_toRat {p : ℕ} (d : Dyadic p) :
    ((d.toRat : ℚ) : ℝ) = d.toReal := by
  rw [Dyadic.toRat, Dyadic.toReal, Rat.cast_mul, Rat.cast_intCast]

end CORALean.Float


namespace CORALean.Float.Dyadic

variable {p : ℕ}


-- ======================================  `toReal_half`  ======================================= --
-- Authors:       Claude Opus 5
-- Written:       16-August-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Dropping the exponent by one, which is what `SoundFloatArithmetic.toReal_half`
needs from `Dyadic`. -/
theorem toReal_half (a : Dyadic p) : toReal (half a) = toReal a / 2 := by
  rw [toReal_def, toReal_def, half, zpow_sub₀ (two_ne_zero), zpow_one]
  ring


-- ====================================  `toReal_le_of_le`  ===================================== --
-- Authors:       Claude Opus 5
-- Written:       16-August-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The direction `SoundFloatArithmetic` asks for; the converse holds too
(`le_iff`), but nothing here needs it. -/
theorem toReal_le_of_le {a b : Dyadic p} (h : le a b = true) : toReal a ≤ toReal b :=
  (le_iff a b).mp h


-- =======================================  `toReal_mk`  ======================================== --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `toReal_def` restated at an anonymous constructor, which is the form
`quotDown_le_div` and `le_quotUp` both rewrite with after computing a quotient. -/
theorem toReal_mk (m e : ℤ) : toReal (⟨m, e⟩ : Dyadic p) = (m : ℝ) * 2 ^ e :=
  toReal_def _


-- =====================================  `toReal_mk_zero`  ===================================== --
-- Authors:       Claude Opus 5
-- Written:       16-August-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Any exponent, since a zero mantissa reads as zero regardless of the scale it
is read at — what `SoundFloatArithmetic.toReal_zero` needs from `Dyadic`. -/
theorem toReal_mk_zero (e : ℤ) : toReal (⟨0, e⟩ : Dyadic p) = 0 := by
  rw [toReal_def, Int.cast_zero, zero_mul]


-- =======================================  `toReal_neg`  ======================================= --
-- Authors:       Claude Opus 5
-- Written:       16-August-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Touching the mantissa alone, which is what `SoundFloatArithmetic.toReal_neg`
needs from `Dyadic`. -/
theorem toReal_neg (d : Dyadic p) : toReal (neg d) = -toReal d := by
  rw [toReal_def, toReal_def, neg, Int.cast_neg, neg_mul]

end CORALean.Float.Dyadic


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

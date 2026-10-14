module

public import CORALean.Global.Float.Instances.FixedPoint.FixedPoint
public import CORALean.Global.Float.Instances.FixedPoint.Operations.Basic
public import CORALean.Global.Float.Instances.FixedPoint.Theorems.LeIff
public import CORALean.Global.Float.Instances.FixedPoint.Theorems.ToRealDef

@[expose] public section

/-!
# `Global/Float/Instances/FixedPoint/Theorems`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float.FixedPoint

variable {f : ℕ}


-- ====================================  `toReal_le_of_le`  ===================================== --
-- Authors:       Claude Opus 5.5
-- Written:       28-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The direction `SoundFloatArithmetic` asks for; the converse holds too
(`le_iff`), but nothing here needs it. -/
theorem toReal_le_of_le {a b : FixedPoint f} (h : le a b = true) : toReal a ≤ toReal b :=
  (le_iff a b).mp h


-- =======================================  `toReal_mk`  ======================================== --
-- Authors:       Claude Opus 5.5
-- Written:       28-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `toReal_def` restated at an anonymous constructor, which is the form every
operation's own guarantee rewrites with after computing a mantissa and digit
count. -/
theorem toReal_mk (m : ℤ) (d : ℕ) : toReal (⟨m, d⟩ : FixedPoint f) = (m : ℝ) / 10 ^ d :=
  toReal_def _


-- =====================================  `toReal_mk_zero`  ===================================== --
-- Authors:       Claude Opus 5.5
-- Written:       28-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Any digit count, since a zero mantissa reads as zero regardless of the scale
it is read at -- what `SoundFloatArithmetic.toReal_zero` needs from
`FixedPoint`. -/
theorem toReal_mk_zero (d : ℕ) : toReal (⟨0, d⟩ : FixedPoint f) = 0 := by
  rw [toReal_def, Int.cast_zero, zero_div]


-- =======================================  `toReal_neg`  ======================================= --
-- Authors:       Claude Opus 5.5
-- Written:       28-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Touching the mantissa alone, which is what `SoundFloatArithmetic.toReal_neg`
needs from `FixedPoint`. -/
theorem toReal_neg (x : FixedPoint f) : toReal (neg x) = -toReal x := by
  rw [toReal_def, toReal_def, neg, Int.cast_neg, neg_div]

end CORALean.Float.FixedPoint


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.Global.Float.Instances.Dyadic.Operations.Basic
public import CORALean.Global.Float.Instances.Dyadic.Theorems.ToRealDef
public import CORALean.Global.Float.Instances.Dyadic.Theorems.ToRealShift
public import Mathlib.Analysis.Normed.Ring.Lemmas

@[expose] public section

/-!
# Rounding up never undershoots

`roundUp` is `roundDown` applied to the negated mantissa, so the ceiling case
is the floor case's fact, `Int.ediv_mul_le`, read back through the same
negation.
-/

-- Authors:       Claude Opus 5
-- Written:       16-August-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float.Dyadic

variable {p : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem le_roundUp (d : Dyadic p) : toReal d ≤ toReal (roundUp d) := by -- --- PROOF ---
  have h : d.mantissa ≤ -(-d.mantissa / 2 ^ d.shift) * 2 ^ d.shift := by
    rw [neg_mul, le_neg]
    exact Int.ediv_mul_le _ (pow_ne_zero _ two_ne_zero)
  rw [roundUp, toReal_shift, toReal_def]
  exact mul_le_mul_of_nonneg_right (Int.cast_le.mpr h) (le_of_lt (zpow_pos two_pos _))

end CORALean.Float.Dyadic


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

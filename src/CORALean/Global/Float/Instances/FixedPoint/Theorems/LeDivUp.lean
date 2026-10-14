module

public import CORALean.Global.Float.Instances.FixedPoint.Operations.Basic
public import CORALean.Global.Float.Instances.FixedPoint.Theorems.MantissaPos
public import CORALean.Global.Float.Instances.FixedPoint.Theorems.Basic
public import Mathlib.Data.Int.ConditionallyCompleteOrder

@[expose] public section

/-!
# Division, rounded up, never undershoots

`DivDownLeDiv`'s mirror: the ceiling is the floor of the negation, and
`Int.ediv_mul_le` applied there gives the same cross-multiplied fact the other
way, read back at `f` digits by `div_le_div_iff₀`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       28-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float.FixedPoint

variable {f : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem le_divUp (a b : FixedPoint f) (hb : 0 < toReal b) :
    toReal a / toReal b ≤ toReal (divUp a b) := by -- --- PROOF ---
  have hm : 0 < b.m := mantissa_pos hb
  have hDZ : (0 : ℤ) < 10 ^ a.d * b.m := by positivity
  have hDR : (0 : ℝ) < 10 ^ a.d * (b.m : ℝ) := by positivity
  have hEq : toReal a / toReal b = ((a.m : ℝ) * 10 ^ b.d) / (10 ^ a.d * (b.m : ℝ)) := by
    rw [toReal_def, toReal_def, div_div_div_eq]
  have h2 : a.m * 10 ^ (b.d + f) ≤
      -(-(a.m * 10 ^ (b.d + f)) / (10 ^ a.d * b.m)) * (10 ^ a.d * b.m) := by
    rw [neg_mul, le_neg]
    exact Int.ediv_mul_le _ hDZ.ne'
  have h3 : (a.m : ℝ) * 10 ^ (b.d + f) ≤
      (↑(-(-(a.m * 10 ^ (b.d + f)) / (10 ^ a.d * b.m))) : ℝ) * (10 ^ a.d * (b.m : ℝ)) := by
    exact_mod_cast h2
  rw [divUp, hEq, toReal_mk, div_le_div_iff₀ hDR (by positivity)]
  calc (a.m : ℝ) * 10 ^ b.d * 10 ^ f
      = (a.m : ℝ) * 10 ^ (b.d + f) := by rw [pow_add]; ring
    _ ≤ _ := h3

end CORALean.Float.FixedPoint


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

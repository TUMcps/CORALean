import CORALean.Global.Float.Instances.FixedPoint.Operations.RoundUp
import CORALean.Global.Float.Instances.FixedPoint.Theorems.ToRealAlign
import CORALean.Global.Float.Instances.FixedPoint.Theorems.ToRealMk
import Mathlib.Data.Int.ConditionallyCompleteOrder

/-!
# Rounding up never undershoots

`RoundDownLe`'s mirror: at or below `f` digits `roundUp` only pads with zeros,
exact by `toReal_align`; past it, the ceiling is the floor of the negation,
and `Int.ediv_mul_le` applied there gives the same fact the other way.
-/

-- Authors:       Claude Opus 5.5
-- Written:       28-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float.FixedPoint

variable {f : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem le_roundUp (x : FixedPoint f) : toReal x ≤ toReal (roundUp x) := by -- --- PROOF ---
  rw [roundUp]
  split
  · next h => exact ((toReal_align x h).trans (toReal_mk _ _).symm).le
  · next h =>
    rw [not_le] at h
    have hpow : (10 : ℝ) ^ x.d = 10 ^ (x.d - f) * 10 ^ f := by
      rw [← pow_add, Nat.sub_add_cancel h.le]
    have h2 : x.m ≤ -(-x.m / 10 ^ (x.d - f)) * 10 ^ (x.d - f) := by
      rw [neg_mul, le_neg]
      exact Int.ediv_mul_le _ (by positivity)
    rw [toReal_def, toReal_mk,
      div_le_div_iff₀ (by positivity : (0:ℝ) < 10 ^ x.d) (by positivity : (0:ℝ) < 10 ^ f), hpow]
    calc (x.m : ℝ) * 10 ^ f
        ≤ (↑(-(-x.m / 10 ^ (x.d - f))) : ℝ) * 10 ^ (x.d - f) * 10 ^ f :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast h2) (by positivity)
      _ = (↑(-(-x.m / 10 ^ (x.d - f))) : ℝ) * (10 ^ (x.d - f) * 10 ^ f) := by ring

end CORALean.Float.FixedPoint


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

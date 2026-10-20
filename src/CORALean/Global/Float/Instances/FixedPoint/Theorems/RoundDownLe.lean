module

public import CORALean.Global.Float.Instances.FixedPoint.Operations.RoundDown
public import CORALean.Global.Float.Instances.FixedPoint.Theorems.Basic
public import CORALean.Global.Float.Instances.FixedPoint.Theorems.ToRealAlign
public import CORALean.Global.Float.Instances.FixedPoint.Theorems.ToRealDef
public import Mathlib.Data.Int.ConditionallyCompleteOrder

@[expose] public section

/-!
# Rounding down never overshoots

At or below `f` digits, `roundDown` only pads with zeros -- exact, so
`toReal_align` gives equality. Past `f`, `Int.ediv_mul_le` is floor division's
own fact -- it never overshoots -- read back at `f` digits by `div_le_div_iff₀`.

## Inputs
* `x` – fixed-point value

## Hypotheses
* none

## Conclusion
* rounding down does not increase the value
-/

-- Authors:       Claude Opus 5.5
-- Written:       28-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float.FixedPoint

variable {f : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem roundDown_le (x : FixedPoint f) : toReal (roundDown x) ≤ toReal x := by -- --- PROOF ---
  rw [roundDown]
  split
  · next h => rw [toReal_mk]; exact (toReal_align x h).symm.le
  · next h =>
    rw [not_le] at h
    have hpow : (10 : ℝ) ^ x.d = 10 ^ (x.d - f) * 10 ^ f := by
      rw [← pow_add, Nat.sub_add_cancel h.le]
    have h2 : (x.m / 10 ^ (x.d - f) : ℤ) * 10 ^ (x.d - f) ≤ x.m :=
      Int.ediv_mul_le _ (by positivity)
    rw [toReal_mk, toReal_def,
      div_le_div_iff₀ (by positivity : (0:ℝ) < 10 ^ f) (by positivity : (0:ℝ) < 10 ^ x.d), hpow]
    calc (↑(x.m / 10 ^ (x.d - f)) : ℝ) * (10 ^ (x.d - f) * 10 ^ f)
        = (↑(x.m / 10 ^ (x.d - f)) : ℝ) * 10 ^ (x.d - f) * 10 ^ f := by ring
      _ ≤ (x.m : ℝ) * 10 ^ f :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast h2) (by positivity)

end CORALean.Float.FixedPoint


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

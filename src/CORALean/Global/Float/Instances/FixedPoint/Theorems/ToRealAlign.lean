module

public import CORALean.Global.Float.Instances.FixedPoint.FixedPoint
public import CORALean.Global.Float.Instances.FixedPoint.Theorems.ToRealDef
public import Mathlib.Tactic.Positivity

@[expose] public section

/-!
# A fixed-point value read at any larger digit count

A value read at any digit count at or above its own, its mantissa padded with
the zeros the extra digits need -- exact, since padding a decimal with zeros
changes nothing it denotes. What `RoundDownLe`/`LeRoundUp` need for the
branch that pads rather than cuts.

## Inputs
* `x` – fixed-point value
* `e` – larger digit count

## Hypotheses
* `h` – the value has at most that many digits

## Conclusion
* the value is its mantissa padded with zeros to that digit count
-/

-- Authors:       Claude Opus 5.5
-- Written:       28-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float.FixedPoint

variable {f : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem toReal_align (x : FixedPoint f) {e : ℕ} (h : x.d ≤ e) :
    toReal x = ((x.m * 10 ^ (e - x.d) : ℤ) : ℝ) / 10 ^ e := by -- --- PROOF ---
  rw [toReal_def]
  have hpow : (10 : ℝ) ^ e = 10 ^ (e - x.d) * 10 ^ x.d := by
    rw [← pow_add, Nat.sub_add_cancel h]
  push_cast
  rw [hpow, div_eq_div_iff (by positivity) (by positivity)]
  ring

end CORALean.Float.FixedPoint


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

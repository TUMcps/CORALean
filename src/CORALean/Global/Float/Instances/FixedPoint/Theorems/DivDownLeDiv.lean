import CORALean.Global.Float.Instances.FixedPoint.Operations.DivDown
import CORALean.Global.Float.Instances.FixedPoint.Theorems.MantissaPos
import CORALean.Global.Float.Instances.FixedPoint.Theorems.ToRealMk

/-!
# Division, rounded down, never overshoots

`toReal a / toReal b` is, cross-multiplied, `a.m · 10 ^ b.d` over
`10 ^ a.d · b.m` -- exactly `divDown`'s divisor -- so `Int.ediv_mul_le` applied
there is the whole fact, read back at `f` digits by `div_le_div_iff₀`. A
positive divisor is what the direction depends on, `mantissa_pos` reading it
off `toReal b`.
-/

-- Authors:       Tobias Ladner
-- Written:       28-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float.FixedPoint

variable {f : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem divDown_le_div (a b : FixedPoint f) (hb : 0 < toReal b) :
    toReal (divDown a b) ≤ toReal a / toReal b := by -- --- PROOF ---
  have hm : 0 < b.m := mantissa_pos hb
  have hDZ : (0 : ℤ) < 10 ^ a.d * b.m := by positivity
  have hDR : (0 : ℝ) < 10 ^ a.d * (b.m : ℝ) := by positivity
  have hEq : toReal a / toReal b = ((a.m : ℝ) * 10 ^ b.d) / (10 ^ a.d * (b.m : ℝ)) := by
    rw [toReal_def, toReal_def, div_div_div_eq]
  have h2 : (a.m * 10 ^ (b.d + f)) / (10 ^ a.d * b.m) * (10 ^ a.d * b.m) ≤
      a.m * 10 ^ (b.d + f) := Int.ediv_mul_le _ hDZ.ne'
  have h3 : (↑((a.m * 10 ^ (b.d + f)) / (10 ^ a.d * b.m)) : ℝ) * (10 ^ a.d * (b.m : ℝ)) ≤
      (a.m : ℝ) * 10 ^ (b.d + f) := by exact_mod_cast h2
  rw [divDown, toReal_mk, hEq, div_le_div_iff₀ (by positivity) hDR]
  calc (↑((a.m * 10 ^ (b.d + f)) / (10 ^ a.d * b.m)) : ℝ) * (10 ^ a.d * (b.m : ℝ))
      ≤ (a.m : ℝ) * 10 ^ (b.d + f) := h3
    _ = (a.m : ℝ) * 10 ^ b.d * 10 ^ f := by rw [pow_add]; ring

end CORALean.Float.FixedPoint


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

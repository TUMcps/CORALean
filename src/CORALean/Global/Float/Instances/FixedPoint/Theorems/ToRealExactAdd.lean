module

public import CORALean.Global.Float.Instances.FixedPoint.Operations.ExactAdd
public import CORALean.Global.Float.Instances.FixedPoint.Theorems.Basic
public import CORALean.Global.Float.Instances.FixedPoint.Theorems.ToRealDef
public import Mathlib.Tactic.Positivity

@[expose] public section

/-!
# Addition is exact

`exactAdd` agrees with ℝ on the nose: it is exactly `div_add_div`'s
cross-multiplied sum read back. What
`SoundFloatArithmetic.add_le_addUp`/`addDown_le_add` compose with the
rounding step to get.

## Inputs
* `a` – first addend
* `b` – second addend

## Hypotheses
* none

## Conclusion
* the exact sum denotes the real sum
-/

-- Authors:       Claude Opus 5.5
-- Written:       28-September-2026
-- Last update:   ---
-- Reviewed:      19-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float.FixedPoint

variable {f : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem toReal_exactAdd (a b : FixedPoint f) : -- --- CONCL ---
    toReal (exactAdd a b) = toReal a + toReal b := by -- --- PROOF ---
  have ha : (10 : ℝ) ^ a.d ≠ 0 := by positivity
  have hb : (10 : ℝ) ^ b.d ≠ 0 := by positivity
  rw [exactAdd, toReal_mk, toReal_def, toReal_def, pow_add, div_add_div _ _ ha hb]
  push_cast
  ring

end CORALean.Float.FixedPoint


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

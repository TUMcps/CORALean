module

public import CORALean.Specification.STLInterval.Operations.PlusNum
public import CORALean.Specification.STLInterval.Theorems.Basic
public import CORALean.Specification.STLInterval.Theorems.RawSetAdd
public import CORALean.Specification.STLInterval.Theorems.RawSetNonemptyOfFields
public import CORALean.Specification.STLInterval.Theorems.SetStlInterval

@[expose] public section

/-!
# `plus` with a number denotes a shift

`I + c` denotes `I` shifted by `c`.

## Inputs
* `I` – interval
* `c` – number

## Hypotheses
* `hc` – the lower bound stays nonnegative

## Conclusion
* the sum denotes the times shifted by the number
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float FloatOps SoundFloatArithmetic


-- =======================================  MAIN THEOREM  ======================================= --

/-- `plusNum` denotes `I` shifted by `c`. -/
theorem STLInterval.set_plusNum (I : STLInterval ℝ) (c : ℝ)
    (hc : I ≠ .empty → 0 ≤ toReal (addDown I.lowerBound c)) : -- --- CONCL ---
    (I.plusNum c hc).set = (fun t => t + c) '' I.set := by -- --- PROOF ---
  cases I with
  | empty => simp [STLInterval.plusNum, STLInterval.set]
  | nonempty l u lc rc b c' _ =>
    simp only [STLInterval.plusNum]
    rw [set_stlInterval, STLInterval.toEReal_map_addUp, toReal_real, addDown_real, EReal.coe_add,
      ← Set.add_singleton, ← Set.Icc_self c, ← rawSet_closed_coe]
    have := rawSet_add (rawSet_nonempty_of_fields b c') (rawSet_closed_nonempty (le_refl c))
    simpa [STLInterval.set] using this

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

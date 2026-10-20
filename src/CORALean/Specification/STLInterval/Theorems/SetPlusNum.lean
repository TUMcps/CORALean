module

public import CORALean.Specification.STLInterval.Operations.PlusNum
public import CORALean.Specification.STLInterval.Theorems.SetStlInterval
public import CORALean.Specification.STLInterval.Theorems.RawSetAdd
public import CORALean.Specification.STLInterval.Theorems.Basic

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

open scoped Pointwise


-- =======================================  MAIN THEOREM  ======================================= --

/-- `plusNum` denotes `I` shifted by `c`. -/
theorem STLInterval.set_plusNum (I : STLInterval) (c : ℝ)
    (hc : I ≠ .empty → 0 ≤ I.lowerBound + c) :
    (I.plusNum c hc).set = (fun t => t + c) '' I.set := by -- --- PROOF ---
  cases I with
  | empty => simp [STLInterval.plusNum, STLInterval.set]
  | nonempty l u lc rc a b c' _ =>
    simp only [STLInterval.plusNum]
    rw [set_stlInterval, ← Set.add_singleton, ← Set.Icc_self c, ← rawSet_closed_coe]
    have := rawSet_add (rawSet_nonempty_of _ _ _ _ a b c') (rawSet_closed_nonempty (le_refl c))
    simpa [STLInterval.set] using this

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

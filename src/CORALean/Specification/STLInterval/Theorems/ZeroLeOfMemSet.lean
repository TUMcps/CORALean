module

public import CORALean.Specification.STLInterval.Operations.Basic
public import Mathlib.Data.EReal.Operations

@[expose] public section

/-!
# The times of an interval are nonnegative

The lower bound of an interval is `≥ 0`, so are all its times.

## Inputs
* `I` – interval
* `t` – time

## Hypotheses
* `ht` – the time lies in the interval

## Conclusion
* the time is nonnegative
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- A time of an interval is `≥ 0`. -/
theorem STLInterval.zero_le_of_mem_set (I : STLInterval) (t : ℝ) (ht : t ∈ I.set) : -- --- CONCL ---
    0 ≤ t := by -- --- PROOF ---
  cases I with
  | empty => exact absurd ht (by simp [STLInterval.set])
  | nonempty l u lc rc a b c z =>
    -- the lower end is at most `t`
    have hl : l ≤ (t : EReal) := by
      simp only [STLInterval.set, STLInterval.rawSet, Set.mem_setOf_eq] at ht
      rcases ht.1 with h | ⟨-, h⟩ <;> [exact h.le; exact h.le]
    exact EReal.coe_nonneg.1 (z.trans hl)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

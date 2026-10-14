module

public import CORALean.Specification.STLInterval.Operations.Basic
public import Mathlib.Data.EReal.Operations

@[expose] public section

/-!
# The times of an interval are at least its lower bound

If the lower bound of an interval is `≥ 0`, so are all its times.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- A time of an interval with lower bound `≥ 0` is `≥ 0`. -/
theorem STLInterval.zero_le_of_mem_set (I : STLInterval)
    (hI : ∀ f, I.fieldsOf = some f → 0 ≤ f.lower) (t : ℝ) (ht : t ∈ I.set) :
    0 ≤ t := by -- --- PROOF ---
  cases I with
  | empty => exact absurd ht (by simp [STLInterval.set])
  | nonempty l u lc rc a b c =>
    -- the lower end is at most `t`
    have hl : l ≤ (t : EReal) := by
      simp only [STLInterval.set, STLInterval.rawSet, Set.mem_setOf_eq] at ht
      rcases ht.1 with h | ⟨-, h⟩ <;> [exact h.le; exact h.le]
    exact EReal.coe_nonneg.1 ((hI _ rfl).trans hl)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

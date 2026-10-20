module

public import CORALean.Specification.STLInterval.Operations.Supremum
public import CORALean.Specification.STLInterval.Theorems.Basic
public import CORALean.Specification.STLInterval.Theorems.RawSetBoundsNe
public import CORALean.Specification.STLInterval.Theorems.RawSetLowerOfGe

@[expose] public section

/-!
# `supremum` says whether the supremum is a time

The flag `supremum` returns holds iff the supremum is itself one of the times.

## Inputs
* `I` – interval

## Hypotheses
* `hI` – the interval is nonempty

## Conclusion
* the supremum is closed iff a time of the interval attains it
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- `isMax` holds iff the supremum is attained by a time of the interval. -/
theorem STLInterval.supremum_closed_iff (I : STLInterval) (hI : I ≠ .empty) : -- --- CONCL ---
    I.supremum.closed = true ↔
      ∃ t ∈ I.set, I.supremum.value = some (t : EReal) := by -- --- PROOF ---
  cases I with
  | empty => exact absurd rfl hI
  | nonempty l u lc rc a b c _ =>
    obtain ⟨x, hx⟩ := rawSet_nonempty_of _ _ _ _ a b c
    show rc = true ↔ ∃ t ∈ rawSet l u lc rc, some u = some (t : EReal)
    constructor
    · intro hc
      have ht : u ≠ ⊤ := fun h => by simp [b h] at hc
      have hb : u ≠ ⊥ := (rawSet_bounds_ne ⟨x, hx⟩).2
      refine ⟨u.toReal, ⟨?_, Or.inr ⟨hc, EReal.coe_toReal ht hb⟩⟩,
        by rw [EReal.coe_toReal ht hb]⟩
      refine rawSet_lower_of_ge ?_ hx.1
      rcases hx.2 with h | ⟨_, h⟩
      · rw [← EReal.coe_le_coe_iff, EReal.coe_toReal ht hb]; exact h.le
      · rw [← EReal.coe_le_coe_iff, EReal.coe_toReal ht hb]; exact h.le
    · rintro ⟨t, ⟨_, h | ⟨hc, _⟩⟩, e⟩
      · exact absurd (Option.some.inj e ▸ h) (lt_irrefl _)
      · exact hc

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

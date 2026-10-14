module

public import CORALean.Specification.STLInterval.Operations.Infimum
public import CORALean.Specification.STLInterval.Theorems.Basic
public import CORALean.Specification.STLInterval.Theorems.RawSetBoundsNe
public import CORALean.Specification.STLInterval.Theorems.RawSetUpperOfLe

@[expose] public section

/-!
# `infimum` says whether the infimum is a time

The flag `infimum` returns holds iff the infimum is itself one of the times.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- `isMin` holds iff the infimum is attained by a time of the interval. -/
theorem STLInterval.infimum_closed_iff (I : STLInterval) (hI : I ≠ .empty) :
    I.infimum.closed = true ↔ ∃ t ∈ I.set, I.infimum.value = some (t : EReal) := by -- --- PROOF ---
  cases I with
  | empty => exact absurd rfl hI
  | nonempty l u lc rc a b c =>
    obtain ⟨x, hx⟩ := set_nonempty _ _ _ _ a b c
    show lc = true ↔ ∃ t ∈ rawSet l u lc rc, some l = some (t : EReal)
    constructor
    · intro hc
      have hb : l ≠ ⊥ := fun h => by simp [a h] at hc
      have ht : l ≠ ⊤ := (rawSet_bounds_ne ⟨x, hx⟩).1
      refine ⟨l.toReal, ⟨Or.inr ⟨hc, (EReal.coe_toReal ht hb).symm⟩, ?_⟩,
        by rw [EReal.coe_toReal ht hb]⟩
      refine rawSet_upper_of_le ?_ hx.2
      rcases hx.1 with h | ⟨_, h⟩
      · rw [← EReal.coe_le_coe_iff, EReal.coe_toReal ht hb]; exact h.le
      · rw [← EReal.coe_le_coe_iff, EReal.coe_toReal ht hb]; exact h.le
    · rintro ⟨t, ⟨h | ⟨hc, _⟩, _⟩, e⟩
      · exact absurd (Option.some.inj e ▸ h) (lt_irrefl _)
      · exact hc

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

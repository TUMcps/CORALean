module

public import CORALean.Specification.STLInterval.STLInterval

@[expose] public section

/-!
# A reach below a time in an STL interval

A nonempty `rawSet` has an element at or below `s` exactly when `s` is above its lower bound: the
lower half of the membership test, on its own. The upper half is `rawSet_upperReach`.

## Inputs
* `l` – lower bound
* `u` – upper bound
* `lc` – lower bound is closed
* `rc` – upper bound is closed
* `s` – time

## Hypotheses
* `hne` – the interval is nonempty

## Conclusion
* a member lies at or below the time iff the time is past the lower bound
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- A nonempty interval reaches down to `s` iff `s` is past its lower bound. -/
theorem STLInterval.rawSet_lowerReach {l u : EReal} {lc rc : Bool}
    (hne : (rawSet l u lc rc).Nonempty)
    (s : ℝ) : (∃ a ∈ rawSet l u lc rc, a ≤ s) ↔ (l < s ∨ (lc = true ∧ l = s)) := by -- --- PROOF ---
  constructor
  · rintro ⟨a, ⟨h1 | ⟨hc, e⟩, _⟩, has⟩
    · exact Or.inl (h1.trans_le (EReal.coe_le_coe_iff.2 has))
    · rcases has.lt_or_eq with h | h
      · exact Or.inl (e ▸ EReal.coe_lt_coe_iff.2 h)
      · exact Or.inr ⟨hc, e.trans (congrArg _ h)⟩
  · intro hs
    obtain ⟨x, hx⟩ := hne
    by_cases hxs : x ≤ s
    · exact ⟨x, hx, hxs⟩
    · refine ⟨s, ⟨hs, ?_⟩, le_rfl⟩
      have := EReal.coe_lt_coe_iff.2 (not_le.1 hxs)
      rcases hx.2 with h | ⟨_, h⟩
      · exact Or.inl (this.trans h)
      · exact Or.inl (h ▸ this)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.Specification.STLInterval.STLInterval

@[expose] public section

/-!
# A reach above a time in an STL interval

A nonempty `rawSet` has an element at or above `s` exactly when `s` is below its upper bound; see
`rawSet_lowerReach`.

## Inputs
* `l` – lower bound
* `u` – upper bound
* `lc` – lower bound is closed
* `rc` – upper bound is closed
* `s` – time

## Hypotheses
* `hne` – the interval is nonempty

## Conclusion
* a member lies at or above the time iff the time is before the upper bound
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- A nonempty interval reaches up to `s` iff `s` is before its upper bound. -/
theorem STLInterval.rawSet_upperReach {l u : EReal} {lc rc : Bool}
    (hne : (rawSet l u lc rc).Nonempty)
    (s : ℝ) : -- --- CONCL ---
    (∃ a ∈ rawSet l u lc rc, s ≤ a) ↔
      ((s : EReal) < u ∨ (rc = true ∧ (s : EReal) = u)) := by -- --- PROOF ---
  constructor
  · rintro ⟨a, ⟨_, h1 | ⟨hc, e⟩⟩, has⟩
    · exact Or.inl ((EReal.coe_le_coe_iff.2 has).trans_lt h1)
    · rcases has.lt_or_eq with h | h
      · exact Or.inl (e ▸ EReal.coe_lt_coe_iff.2 h)
      · exact Or.inr ⟨hc, e ▸ congrArg _ h⟩
  · intro hs
    obtain ⟨x, hx⟩ := hne
    by_cases hxs : s ≤ x
    · exact ⟨x, hx, hxs⟩
    · refine ⟨s, ⟨?_, hs⟩, le_rfl⟩
      have := EReal.coe_lt_coe_iff.2 (not_le.1 hxs)
      rcases hx.1 with h | ⟨_, h⟩
      · exact Or.inl (h.trans this)
      · exact Or.inl (h ▸ this)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

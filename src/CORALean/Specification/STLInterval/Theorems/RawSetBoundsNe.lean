module

public import CORALean.Specification.STLInterval.STLInterval

@[expose] public section

/-!
# A nonempty interval has a bounded lower and upper end

The lower bound of a nonempty `rawSet` is not `+∞` and its upper bound is not `-∞`.

## Inputs
* `l` – lower bound
* `u` – upper bound
* `lc` – lower bound is closed
* `rc` – upper bound is closed

## Hypotheses
* `hne` – the interval is nonempty

## Conclusion
* the lower bound is not top and the upper bound not bottom
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- A nonempty interval's lower bound is not `⊤`, its upper bound not `⊥`. -/
theorem STLInterval.rawSet_bounds_ne {l u : EReal} {lc rc : Bool}
    (hne : (rawSet l u lc rc).Nonempty) : -- --- CONCL ---
    l ≠ ⊤ ∧ u ≠ ⊥ := by -- --- PROOF ---
  obtain ⟨x, h1, h2⟩ := hne
  constructor
  · rintro rfl
    rcases h1 with h | ⟨_, h⟩
    · exact absurd h (not_lt_of_ge le_top)
    · exact EReal.coe_ne_top x h.symm
  · rintro rfl
    rcases h2 with h | ⟨_, h⟩
    · exact absurd h (not_lt_of_ge bot_le)
    · exact EReal.coe_ne_bot x h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

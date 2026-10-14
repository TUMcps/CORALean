module

public import CORALean.Specification.STLInterval.STLInterval

@[expose] public section

/-!
# The lower end of an STL interval above a member

A time at or above a time that passes the lower test passes it.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- A time at or above one that is past the lower end is past it. -/
theorem STLInterval.rawSet_lower_of_ge {l : EReal} {lc : Bool} {t x : ℝ} (h : x ≤ t)
    (hx : l < x ∨ (lc = true ∧ l = x)) : l < t ∨ (lc = true ∧ l = t) := by -- --- PROOF ---
  rcases h.lt_or_eq with h | rfl
  · rcases hx with hx | ⟨hc, hx⟩
    · exact Or.inl (hx.trans (EReal.coe_lt_coe_iff.2 h))
    · exact Or.inl (hx ▸ EReal.coe_lt_coe_iff.2 h)
  · exact hx

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

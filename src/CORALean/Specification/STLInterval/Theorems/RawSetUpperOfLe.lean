module

public import CORALean.Specification.STLInterval.STLInterval

@[expose] public section

/-!
# The upper end of an STL interval below a member

A time at or below a time that passes the upper test passes it.

## Inputs
* `u` – upper bound
* `rc` – upper bound is closed
* `t` – time
* `x` – member time

## Hypotheses
* `h` – the time is not above the member
* `hx` – the member is before the upper bound

## Conclusion
* the time is before the upper bound
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- A time at or below one that is before the upper end is before it. -/
theorem STLInterval.rawSet_upper_of_le {u : EReal} {rc : Bool} {t x : ℝ} (h : t ≤ x)
    (hx : (x : EReal) < u ∨ (rc = true ∧ (x : EReal) = u)) :
    (t : EReal) < u ∨ (rc = true ∧ (t : EReal) = u) := by -- --- PROOF ---
  rcases h.lt_or_eq with h | rfl
  · rcases hx with hx | ⟨hc, hx⟩
    · exact Or.inl ((EReal.coe_lt_coe_iff.2 h).trans hx)
    · exact Or.inl (hx ▸ EReal.coe_lt_coe_iff.2 h)
  · exact hx

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

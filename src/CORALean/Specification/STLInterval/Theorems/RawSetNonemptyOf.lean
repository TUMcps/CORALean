module

public import CORALean.Specification.STLInterval.STLInterval

@[expose] public section

/-!
# What makes an STL interval nonempty

The invariants of `STLInterval.nonempty` (an infinite bound is open, `lower < upper` or a closed
point) leave a time in the set: a real between the bounds, or the point itself.

## Inputs
* `l` – lower bound
* `u` – upper bound
* `lc` – lower bound is closed
* `rc` – upper bound is closed

## Hypotheses
* `h1` – an infinite lower bound is open
* `h2` – an infinite upper bound is open
* `h3` – the bounds leave a time in the interval

## Conclusion
* the set between the bounds is nonempty
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- The conditions of `STLInterval.nonempty` leave a time in the interval. -/
theorem STLInterval.rawSet_nonempty_of (l u : EReal) (lc rc : Bool) (h1 : l = ⊥ → lc = false)
    (h2 : u = ⊤ → rc = false) (h3 : l < u ∨ (l = u ∧ lc = true ∧ rc = true)) :
    (rawSet l u lc rc).Nonempty := by -- --- PROOF ---
  rcases h3 with h | ⟨e, hc, hr⟩
  · obtain ⟨y, hy1, hy2⟩ := EReal.exists_between_coe_real h
    exact ⟨y, Or.inl hy1, Or.inl hy2⟩
  · subst e
    have hb : l ≠ ⊥ := fun h => by simp [h1 h] at hc
    have ht : l ≠ ⊤ := fun h => by simp [h2 h] at hr
    exact ⟨l.toReal, Or.inr ⟨hc, (EReal.coe_toReal ht hb).symm⟩,
      Or.inr ⟨hr, EReal.coe_toReal ht hb⟩⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

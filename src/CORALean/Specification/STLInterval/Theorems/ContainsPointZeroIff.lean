module

public import CORALean.Specification.STLInterval.Definitions.ContainsPoint
public import CORALean.Specification.STLInterval.Theorems.WithinTolZero
public import CORALean.Specification.STLInterval.Theorems.Basic
public import CORALean.Specification.STLInterval.Theorems.RawSetUpperOfLe
public import CORALean.Specification.STLInterval.Theorems.RawSetLowerOfGe

@[expose] public section

/-!
# `contains_` of a point is membership

At `tol = 0` the numeric branch of `contains_` is membership in the set of times.

## Inputs
* `I` – interval
* `t` – time

## Hypotheses
* none

## Conclusion
* the point test without tolerance is membership
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- `contains_` of a time `t` at `tol = 0` iff `t` is in the interval. -/
theorem STLInterval.containsPoint_zero_iff (I : STLInterval) (t : ℝ) :
    I.containsPoint 0 t ↔ t ∈ I.set := by -- --- PROOF ---
  cases I with
  | empty => simp [STLInterval.containsPoint, STLInterval.set]
  | nonempty l u lc rc a b c _ =>
    obtain ⟨x, hx⟩ := rawSet_nonempty_of _ _ _ _ a b c
    simp only [STLInterval.containsPoint, withinTol_zero]
    show _ ↔ (_ ∧ _)
    constructor
    -- a time strictly inside, or at a closed end, is in the set
    · rintro (⟨h1, h2⟩ | ⟨hc, e⟩ | ⟨hc, e⟩)
      · exact ⟨Or.inl h1, Or.inl h2⟩
      · refine ⟨Or.inr ⟨hc, e⟩, rawSet_upper_of_le ?_ hx.2⟩
        rcases hx.1 with h | ⟨_, h⟩
        · exact EReal.coe_le_coe_iff.1 (e ▸ h.le)
        · exact EReal.coe_le_coe_iff.1 (e ▸ h.le)
      · refine ⟨rawSet_lower_of_ge ?_ hx.1, Or.inr ⟨hc, e.symm⟩⟩
        rcases hx.2 with h | ⟨_, h⟩
        · exact EReal.coe_le_coe_iff.1 (e ▸ h.le)
        · exact EReal.coe_le_coe_iff.1 (e ▸ h.le)
    -- and a member passes the test of the branch that matches it
    · rintro ⟨h1 | ⟨hc, e⟩, h2 | ⟨hc', e'⟩⟩
      · exact Or.inl ⟨h1, h2⟩
      · exact Or.inr (Or.inr ⟨hc', e'.symm⟩)
      · exact Or.inr (Or.inl ⟨hc, e⟩)
      · exact Or.inr (Or.inl ⟨hc, e⟩)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

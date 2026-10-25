module

public import CORALean.Specification.STLInterval.Definitions.IsWithinTol

@[expose] public section

/-!
# `IsWithinTol` at tolerance zero

At `tol = 0` `IsWithinTol` is equality.

## Inputs
* `a` – first value
* `b` – second value

## Hypotheses
* none

## Conclusion
* without tolerance the values agree iff they are equal
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- `IsWithinTol 0 a b` iff `a = b`. -/
theorem STLInterval.withinTol_zero (a b : EReal) : -- --- CONCL ---
    STLInterval.IsWithinTol 0 a b ↔ a = b := by -- --- PROOF ---
  constructor
  · rintro (⟨x, y, rfl, rfl, h | h⟩ | ⟨h, _⟩)
    · have : x = y := sub_eq_zero.1 (abs_nonpos_iff.1 h)
      rw [this]
    · have : x = y := sub_eq_zero.1 (abs_nonpos_iff.1 (by simpa using h))
      rw [this]
    · exact h
  · rintro rfl
    induction a using EReal.rec with
    | bot => exact Or.inr ⟨rfl, Or.inr rfl⟩
    | top => exact Or.inr ⟨rfl, Or.inl rfl⟩
    | coe x => exact Or.inl ⟨x, x, rfl, rfl, Or.inl (by simp)⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# A point's reciprocal lies between the reciprocals of the bounds

For `0 < a ≤ y ≤ b` or `a ≤ y ≤ b < 0` the reciprocal is antitone on the side of `0` the point
lies on, so `b⁻¹ ≤ y⁻¹ ≤ a⁻¹`. The scalar fact behind `Interval.recip`, on both signs.

## Inputs
* `a` – lower bound
* `b` – upper bound
* `y` – point of the interval

## Hypotheses
* `h` – interval does not contain zero
* `h₁` – lower bound below `y`
* `h₂` – `y` below the upper bound

## Conclusion
* the reciprocal of `y` lies between the reciprocals of the bounds
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- The reciprocal of a point between `a` and `b` is between their reciprocals, swapped. -/
theorem Interval.inv_between {a b y : ℝ} (h : 0 < a ∨ b < 0) (h₁ : a ≤ y) (h₂ : y ≤ b) :
    b⁻¹ ≤ y⁻¹ ∧ y⁻¹ ≤ a⁻¹ := by -- --- PROOF ---
  rcases h with ha | hb
  · exact ⟨inv_anti₀ (ha.trans_le h₁) h₂, inv_anti₀ ha h₁⟩
  · have hy : y < 0 := lt_of_le_of_lt h₂ hb
    have ha : a < 0 := lt_of_le_of_lt h₁ hy
    exact ⟨(inv_le_inv_of_neg hb hy).mpr h₂, (inv_le_inv_of_neg hy ha).mpr h₁⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

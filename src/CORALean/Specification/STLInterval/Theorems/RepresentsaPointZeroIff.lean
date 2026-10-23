module

public import CORALean.Specification.STLInterval.Definitions.Representsa
public import CORALean.Specification.STLInterval.Theorems.WithinTolZero
public import CORALean.Specification.STLInterval.Theorems.SetEqSingletonIff

@[expose] public section

/-!
# `representsa_` as `point`

At `tol = 0` `representsa_(I,'point')` holds iff `I` denotes a single time.

## Inputs
* `I` – interval

## Hypotheses
* none

## Conclusion
* the interval represents a point iff its times are a singleton
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float FloatOps SoundFloatArithmetic


-- =======================================  MAIN THEOREM  ======================================= --

/-- `representsa_ point` at `tol = 0` iff the set of times is a singleton. -/
theorem STLInterval.representsa_point_zero_iff (I : STLInterval ℝ) : -- --- CONCL ---
    I.representsa_ 0 .point ↔ ∃ x : ℝ, I.set = {x} := by -- --- PROOF ---
  cases I with
  | empty => simp [STLInterval.representsa_, STLInterval.set]
  | nonempty l u lc rc b c z =>
    simp only [STLInterval.representsa_, withinTol_zero, set_eq_singleton_iff b c z, toReal_real]
    constructor
    · -- a radius `0` makes the upper bound the lower one
      rintro ⟨hc, hr, y, hy, h⟩
      have hyl : y = l := by
        have := EReal.coe_eq_zero.1 h
        linarith
      subst hyl
      cases u with
      | top => simp at hy
      | coe x =>
        simp only [STLInterval.toEReal_coe, toReal_real, EReal.coe_eq_coe_iff] at hy
        exact ⟨y, rfl, by rw [hy], hc, hr⟩
    · rintro ⟨x, rfl, rfl, hc, hr⟩
      exact ⟨hc, hr, l, by simp, by simp⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

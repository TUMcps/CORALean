module

public import CORALean.Specification.STLInterval.Definitions.Representsa
public import CORALean.Specification.STLInterval.Theorems.WithinTolZero
public import CORALean.Specification.STLInterval.Theorems.SetEqSingletonIff

@[expose] public section

/-!
# `representsa_` as `point`

At `tol = 0` `representsa_(I,'point')` holds iff `I` denotes a single time.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- `representsa_ point` at `tol = 0` iff the set of times is a singleton. -/
theorem STLInterval.representsa_point_zero_iff (I : STLInterval) :
    I.representsa_ 0 .point ↔ ∃ x : ℝ, I.set = {x} := by -- --- PROOF ---
  cases I with
  | empty => simp [STLInterval.representsa_, STLInterval.set]
  | nonempty l u lc rc a b c =>
    simp only [STLInterval.representsa_, withinTol_zero, set_eq_singleton_iff a b c]
    constructor
    · rintro ⟨hc, hr, x, y, rfl, rfl, h⟩
      have : y = x := by
        have h' : y - x = 0 := by
          have := EReal.coe_eq_zero.1 h
          linarith
        linarith
      subst this
      exact ⟨y, rfl, rfl, hc, hr⟩
    · rintro ⟨x, rfl, rfl, hc, hr⟩
      exact ⟨hc, hr, x, x, rfl, rfl, by simp⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

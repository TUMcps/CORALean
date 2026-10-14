module

public import CORALean.Specification.STLInterval.Definitions.Representsa
public import CORALean.Specification.STLInterval.Theorems.WithinTolZero
public import CORALean.Specification.STLInterval.Theorems.SetEqSingletonIff

@[expose] public section

/-!
# `representsa_` as `origin`

At `tol = 0` `representsa_(I,'origin')` holds iff `I` denotes `{0}`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- `representsa_ origin` at `tol = 0` iff the set of times is `{0}`. -/
theorem STLInterval.representsa_origin_zero_iff (I : STLInterval) :
    I.representsa_ 0 .origin ↔ I.set = {0} := by -- --- PROOF ---
  cases I with
  | empty => simp [STLInterval.representsa_, STLInterval.set]
  | nonempty l u lc rc a b c =>
    simp only [STLInterval.representsa_, withinTol_zero, set_eq_singleton_iff a b c]
    simp only [EReal.coe_zero]
    tauto

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

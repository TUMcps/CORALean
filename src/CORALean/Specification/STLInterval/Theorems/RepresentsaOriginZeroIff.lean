module

public import CORALean.Specification.STLInterval.Definitions.Representsa
public import CORALean.Specification.STLInterval.Theorems.WithinTolZero
public import CORALean.Specification.STLInterval.Theorems.SetEqSingletonIff

@[expose] public section

/-!
# `representsa_` as `origin`

At `tol = 0` `representsa_(I,'origin')` holds iff `I` denotes `{0}`.

## Inputs
* `I` – interval

## Hypotheses
* none

## Conclusion
* the interval represents the origin iff its times are zero alone
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float FloatOps SoundFloatArithmetic


-- =======================================  MAIN THEOREM  ======================================= --

/-- `representsa_ origin` at `tol = 0` iff the set of times is `{0}`. -/
theorem STLInterval.representsa_origin_zero_iff (I : STLInterval ℝ) : -- --- CONCL ---
    I.representsa_ 0 .origin ↔ I.set = {0} := by -- --- PROOF ---
  cases I with
  | empty => simp [STLInterval.representsa_, STLInterval.set]
  | nonempty l u lc rc b c z =>
    simp only [STLInterval.representsa_, withinTol_zero, set_eq_singleton_iff b c z, toReal_real,
      EReal.coe_eq_zero]
    -- the upper bound reads as `0` exactly when it is the stored `0`
    cases u with
    | top => simp
    | coe x => simp only [STLInterval.toEReal_coe, toReal_real, EReal.coe_eq_zero,
        WithTop.coe_eq_coe]; tauto

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

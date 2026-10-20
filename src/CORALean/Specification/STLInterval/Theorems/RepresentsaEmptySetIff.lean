module

public import CORALean.Specification.STLInterval.Definitions.Representsa
public import CORALean.Specification.STLInterval.Theorems.Basic

@[expose] public section

/-!
# `representsa_` as `emptySet`

`representsa_(I,'emptySet')` holds iff `I` denotes no time.

## Inputs
* `tol` – tolerance
* `I` – interval

## Hypotheses
* none

## Conclusion
* the interval represents the empty set iff its times are empty
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- `representsa_ emptySet` iff the set of times is empty. -/
theorem STLInterval.representsa_emptySet_iff (tol : ℝ) (I : STLInterval) :
    I.representsa_ tol .emptySet ↔ I.set = ∅ := by
  cases I with
  | empty => simp [STLInterval.representsa_, STLInterval.set]
  | nonempty l u lc rc a b c _ =>
    exact iff_of_false id (Set.nonempty_iff_ne_empty.1 (rawSet_nonempty_of _ _ _ _ a b c))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

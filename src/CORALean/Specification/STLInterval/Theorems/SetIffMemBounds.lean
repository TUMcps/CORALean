module

public import CORALean.Specification.STLInterval.Operations.Basic
public import CORALean.Specification.STLInterval.Theorems.Basic
public import CORALean.Specification.STLInterval.Definitions.IsInBounds
public import CORALean.Specification.STLInterval.Definitions.Fields
public import Mathlib.Data.EReal.Operations

@[expose] public section

/-!
# The times of an interval are those between its real bounds

For an interval whose lower bound is `≥ 0` (CORA's constructor throws otherwise), `set` is the set
`IsInBounds` of the real bounds and closedness flags read off the interval; the empty interval gets
the empty `[0,0)`.

## Inputs
* `I` – interval
* `t` – time

## Hypotheses
* none

## Conclusion
* the time is in the interval iff it lies between the real bounds
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem STLInterval.set_iff_memBounds (I : STLInterval ℝ) (t : ℝ) : -- --- CONCL ---
    t ∈ I.set ↔ STLInterval.IsInBounds I.lowerBound I.upperBound I.lowerClosed I.upperClosed t
      := by -- --- PROOF ---
  induction I with
  -- the empty interval has no member, and its bounds `0, 0` open exclude every `t ≥ 0`
  | empty =>
    simp [STLInterval.set, STLInterval.IsInBounds, STLInterval.lowerBound, STLInterval.upperBound,
      STLInterval.lowerClosed, STLInterval.upperClosed, not_lt]
    exact fun h => h.le
  | nonempty l u lc rc h2 h3 h0 =>
    -- case on the upper end, then unfold both sides to the same inequalities
    cases u with
    | top =>
      simp [STLInterval.set, STLInterval.rawSet, STLInterval.IsInBounds, STLInterval.lowerBound,
        STLInterval.upperBound, STLInterval.lowerClosed, STLInterval.upperClosed, eq_comm]
    | coe b =>
      simp [STLInterval.set, STLInterval.rawSet, STLInterval.IsInBounds, STLInterval.lowerBound,
        STLInterval.upperBound, STLInterval.lowerClosed, STLInterval.upperClosed, eq_comm]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

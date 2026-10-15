module

public import Mathlib.Data.EReal.Operations

@[expose] public section

/-!
# CORA's `stlInterval`: time intervals with open and closed ends

`specification/@stlInterval/stlInterval.m`: a one-dimensional interval of time with a lower and an
upper bound, each open or closed, or the empty interval (`lower = []`). `STLInterval.nonempty`
carries what the constructor `stlInterval(lb,ub,lc,rc)` establishes: an infinite bound is open,
`lb > ub`, or `lb = ub` with an open end, is empty, and `lb ≥ 0`. `set` is the times denoted.

Bounds are `EReal`, MATLAB's doubles with `±Inf`. The constructor throws on `lb < 0` when
`CHECKS_ENABLED` (the default) and every operation builds through it, so no `stlInterval` has a
negative lower bound: `zero_le` is a field of `nonempty`, and a construction CORA rejects needs
the hypothesis `0 ≤ lb`. With `CHECKS_ENABLED` off CORA accepts one; that is not modelled.

`rawSet` is the set of times between any two bounds, `set` that of an interval's own. They stay
apart because operations compute bounds outside `[0, ∞]` before the constructor clamps or rejects
them (`lower - upper'` in `minus`), and `rawSet_add`, `rawSet_sub` and `rawSet_clamp` are about
those, before any `nonempty` exists.

The intervals are those of [1, Sec. 2.1 (intervals)]: real or infinite bounds, infinite ones open.

## References

* [1] F. Lercher and M. Althoff. "Using Four-Valued Signal Temporal Logic for Incremental
      Verification of Hybrid Systems". CAV, LNCS 14683, pp. 259-281, 2024.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

inductive STLInterval
  | empty
  | nonempty (lower upper : EReal) (leftClosed rightClosed : Bool)
      (lower_open : lower = ⊥ → leftClosed = false)
      (upper_open : upper = ⊤ → rightClosed = false)
      (lt_or_point : lower < upper ∨ (lower = upper ∧ leftClosed = true ∧ rightClosed = true))
      (zero_le : 0 ≤ lower)

/-- The times between the bounds `l` and `u`, each end in when its flag is set; any pair of bounds,
not only those of an `stlInterval` (see the module docstring). -/
def STLInterval.rawSet (l u : EReal) (lc rc : Bool) : Set ℝ :=
  {t | (l < t ∨ (lc = true ∧ l = t)) ∧ ((t : EReal) < u ∨ (rc = true ∧ (t : EReal) = u))}

/-- The times an `stlInterval` denotes. -/
def STLInterval.set : STLInterval → Set ℝ
  | .empty => ∅
  | .nonempty l u lc rc _ _ _ _ => STLInterval.rawSet l u lc rc

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

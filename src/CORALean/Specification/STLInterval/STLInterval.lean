module

public import Mathlib.Data.EReal.Operations

@[expose] public section

/-!
# CORA's `stlInterval`: time intervals with open and closed ends

`specification/@stlInterval/stlInterval.m`: a one-dimensional interval of time with a lower and an
upper bound, each open or closed, or the empty interval (`lower = []`). `STLInterval.nonempty`
carries what the constructor `stlInterval(lb,ub,lc,rc)` establishes: an infinite bound is open, and
`lb > ub`, or `lb = ub` with an open end, is the empty interval. `set` is the set of times
denoted.

Bounds are `EReal`, MATLAB's doubles with `±Inf`. CORA throws on `lb < 0` when `CHECKS_ENABLED`
(the default); the type is the unchecked class, which agrees with CORA wherever it does not throw.

The intervals are those of [1, Sec. 2.1 (intervals)]: bounds in `ℝ` or infinite, and an infinite
one is open.

## References

* [1] F. Lercher and M. Althoff. "Using Four-Valued Signal Temporal Logic for Incremental
      Verification of Hybrid Systems". CAV, LNCS 14683, pp. 259-281, 2024.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
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

/-- The times between the bounds `l` and `u`, each end in when its flag is set. -/
def STLInterval.rawSet (l u : EReal) (lc rc : Bool) : Set ℝ :=
  {t | (l < t ∨ (lc = true ∧ l = t)) ∧ ((t : EReal) < u ∨ (rc = true ∧ (t : EReal) = u))}

/-- The times an `stlInterval` denotes. -/
def STLInterval.set : STLInterval → Set ℝ
  | .empty => ∅
  | .nonempty l u lc rc _ _ _ => STLInterval.rawSet l u lc rc

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

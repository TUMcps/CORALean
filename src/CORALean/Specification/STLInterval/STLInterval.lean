module

public import Mathlib.Data.EReal.Operations

@[expose] public section

/-!
# CORA's `stlInterval`: time intervals with open and closed ends

`specification/@stlInterval/stlInterval.m`: a time interval with open or closed ends, or the empty
one. `STLInterval.nonempty` carries what `stlInterval(lb,ub,lc,rc)` establishes (an infinite bound
is open, `lb > ub` or `lb = ub` with an open end is empty, `lb ≥ 0`); `set` is the times denoted.
Bounds are `EReal`. CORA's constructor throws on `lb < 0` (`CHECKS_ENABLED`, not modelled when off),
so `zero_le` is a field and a construction needs `0 ≤ lb`. `rawSet` is the times between any two
bounds, as operations compute bounds outside `[0, ∞]` before clamping (`rawSet_add`, `rawSet_sub`,
`rawSet_clamp`). The intervals are those of [1, Sec. 2.1 (intervals)].

## References

* [1] F. Lercher and M. Althoff. "Using Four-Valued Signal Temporal Logic for Incremental
      Verification of Hybrid Systems". CAV, LNCS 14683, pp. 259-281, 2024.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   15-October-2026
-- Reviewed:      15-October-2026 (Tobias Ladner)


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

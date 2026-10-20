module

public import CORALean.Specification.PointSegmentSignal.Operations.Basic
public import CORALean.Specification.PointSegmentSignal.Operations.SuccTimeAtValIdx

@[expose] public section

/-!
# The time after the last stored value

The time after the value `b` (zero-based) is `inf` when there is no further time point.

## Inputs
* `T` – time type
* `s` – signal
* `b` – value index

## Hypotheses
* `hk` – there is no further time point

## Conclusion
* the time after the value is infinity, open iff the index is odd
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- The time after the last value is `inf`, open if `b` is odd. -/
theorem PointSegmentSignal.succTimeAtValIdx_of_ge {T : Type} [Zero T] (s : PointSegmentSignal T)
    (b : ℕ) (hk : s.timePoints.length ≤ (b + 1) / 2) :
    s.succTimeAtValIdx (b + 1) = (⊤, decide (b % 2 = 0)) := by
  simp only [PointSegmentSignal.succTimeAtValIdx, PointSegmentSignal.length]
  exact Prod.ext (by simp; omega) (decide_eq_decide.2 (by omega))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

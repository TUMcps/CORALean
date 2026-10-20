module

public import CORALean.Specification.PointSegmentSignal.Operations.Basic
public import CORALean.Specification.PointSegmentSignal.Operations.SuccTimeAtValIdx

@[expose] public section

/-!
# The time after a stored value

The time point after the value `b` (zero-based) is the `(b + 1) / 2`-th time point, open if `b` is
odd, when there is one.

## Inputs
* `T` – time type
* `s` – signal
* `b` – value index

## Hypotheses
* `hk` – a further time point exists

## Conclusion
* the time after the value is that time point, open iff the index is odd
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- The time after the value `b` (zero-based) is a time point, open if `b` is odd. -/
theorem PointSegmentSignal.succTimeAtValIdx_of_lt {T : Type} [Zero T] (s : PointSegmentSignal T)
    (b : ℕ) (hk : (b + 1) / 2 < s.timePoints.length) :
    s.succTimeAtValIdx (b + 1) =
      (((s.timePoints[(b + 1) / 2] : T) : WithTop T), decide (b % 2 = 0)) := by
  simp only [PointSegmentSignal.succTimeAtValIdx, PointSegmentSignal.length]
  refine Prod.ext ?_ (decide_eq_decide.2 (by omega))
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, show ¬ (b + 1) / 2 + 1 >
    s.timePoints.length by omega]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

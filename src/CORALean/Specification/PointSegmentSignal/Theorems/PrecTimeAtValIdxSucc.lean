module

public import CORALean.Specification.PointSegmentSignal.Operations.Basic

@[expose] public section

/-!
# The time before a stored value

The time point before the value `a` (zero-based) is the `a / 2`-th time point, closed (a point
value) if `a` is even.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- The time before the value `a` (zero-based): the `a / 2`-th time point, closed if `a` is even. -/
theorem PointSegmentSignal.precTimeAtValIdx_succ {T : Type} [Zero T] (s : PointSegmentSignal T)
    (a : ℕ) (hk : a / 2 < s.timePoints.length) :
    s.precTimeAtValIdx (a + 1) = (s.timePoints[a / 2], decide (a % 2 = 0)) := by
  simp only [PointSegmentSignal.precTimeAtValIdx, show (a + 1 + 1) / 2 - 1 = a / 2 by omega]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
  omega

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

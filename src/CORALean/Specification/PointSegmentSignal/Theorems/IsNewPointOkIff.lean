module

public import CORALean.Specification.PointSegmentSignal.Operations.IsNewPointOk

@[expose] public section

/-!
# When a new point is needed

`isNewPointOk` unfolded: at a time point the point must be `0` or differ from the intervals around
it, inside an interval some value must differ from the interval's.

## Inputs
* `s` – signal
* `i` – index of the next time point
* `p` – time of the new point
* `vals` – point and interval values of the new point

## Hypotheses
* none

## Conclusion
* a new point is needed iff the stated conditions hold
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {T : Type} [LinearOrder T] [Zero T]


-- =======================================  MAIN THEOREM  ======================================= --

/-- `aux_isNewPointOk` as a proposition. -/
theorem PointSegmentSignal.isNewPointOk_iff (s : PointSegmentSignal T) (i : ℕ) (p : T)
    (vals : List Bool) : -- --- CONCL ---
    s.isNewPointOk i p vals = true ↔ (s.timePoints.getD (i - 1) 0 = p ∧ (p = 0 ∨ vals.getD 0 false ≠
      vals.getD 1 false ∨ vals.getD 0 false ≠ s.precIntervalValue i)) ∨
      (s.timePoints.getD (i - 1) 0 ≠ p ∧ ∃ v ∈ vals, v ≠ s.succIntervalValue i)
      := by -- --- PROOF ---
  unfold PointSegmentSignal.isNewPointOk
  by_cases h : s.timePoints.getD (i - 1) 0 = p
  · simp only [h, if_true, decide_eq_true_eq, true_and, ne_eq, not_true_eq_false, false_and,
      or_false]
  · simp only [h, if_false, List.any_eq_true, decide_eq_true_eq, ne_eq, not_false_eq_true,
      true_and, false_and, false_or]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

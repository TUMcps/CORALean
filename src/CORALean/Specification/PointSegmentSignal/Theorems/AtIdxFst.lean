module

public import CORALean.Specification.PointSegmentSignal.Operations.AtIdx
public import CORALean.Specification.PointSegmentSignal.Theorems.AtBetween
public import CORALean.Specification.PointSegmentSignal.Theorems.AtTimePoint
public import CORALean.Specification.PointSegmentSignal.Theorems.Basic
public import CORALean.Specification.PointSegmentSignal.Theorems.TakeWhileLePos

@[expose] public section

/-!
# The value atIdx returns is the value of the signal

For a valid signal and `u ≥ 0`, the value `atIdx` returns at `u` is `obj.at(u)`.

## Inputs
* `s` – signal
* `u` – time

## Hypotheses
* `hs` – the signal is valid
* `h0` – the time is nonnegative

## Conclusion
* the value from `atIdx` is the value at the time
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {T : Type} [LinearOrder T] [Zero T]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The value `atIdx` returns is the value at the time. -/
theorem PointSegmentSignal.atIdx_fst (s : PointSegmentSignal T) (hs : s.IsValid) (u : T)
    (h0 : 0 ≤ u) : -- --- CONCL ---
    (s.atIdx (u : WithTop T)).1 = s.at u := by -- --- PROOF ---
  obtain ⟨hi1, hi2, ⟨a, ha, hale⟩, hnext⟩ := PointSegmentSignal.takeWhile_le_pos s hs u h0
  have hg : s.timePoints.getD ((s.timePoints.takeWhile (· ≤ u)).length - 1) 0 = a := by
    simp [List.getD_eq_getElem?_getD, ha]
  simp only [TimeOrder.isEqvTop_iff_eq, PointSegmentSignal.atIdx, WithTop.coe_le_coe, hg,
    WithTop.coe_inj]
  rcases hale.lt_or_eq with hlt | heq
  · rw [if_neg hlt.ne]
    have := s.at_between hs _ a u ha hlt
      (by rw [show (s.timePoints.takeWhile (· ≤ u)).length - 1 + 1 =
        (s.timePoints.takeWhile (· ≤ u)).length by omega]; exact hnext)
    rw [this, show (s.timePoints.takeWhile (· ≤ u)).length - 1 + 1 =
      (s.timePoints.takeWhile (· ≤ u)).length by omega]
  · subst heq
    rw [if_pos rfl]
    have := s.at_timePoint hs _ a ha
    rw [this, show (s.timePoints.takeWhile (· ≤ a)).length - 1 + 1 =
      (s.timePoints.takeWhile (· ≤ a)).length by omega]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

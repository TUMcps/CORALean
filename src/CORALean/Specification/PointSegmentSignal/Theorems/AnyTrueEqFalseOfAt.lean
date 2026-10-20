module

public import CORALean.Specification.PointSegmentSignal.Operations.AnyTrue
public import CORALean.Specification.PointSegmentSignal.Theorems.AtBetween
public import CORALean.Specification.PointSegmentSignal.Theorems.AtTimePoint
public import CORALean.Specification.PointSegmentSignal.Theorems.ListLtOfPairwiseGetElemSucc
public import CORALean.Specification.PointSegmentSignal.Theorems.NonnegOfMemTimePoints
public import Mathlib.Order.Interval.Set.Basic

@[expose] public section

/-!
# A signal that is false everywhere has no true value

If a valid signal is `false` at every time, `anyTrue` is `false` on every interval: every stored
value is the value at some time (a time point, one strictly between two, or one after the last).

## Inputs
* `T` – time type
* `s` – signal
* `lb` – interval lower bound
* `ub` – interval upper bound
* `lc` – lower bound is closed
* `rc` – upper bound is closed

## Hypotheses
* `hs` – the signal is valid
* `h` – the signal is false at all times

## Conclusion
* `anyTrue` returns false
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {T : Type} [LinearOrder T] [Zero T]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- All stored values of a signal that is false everywhere are false. -/
theorem aux_values_false_of_at [DenselyOrdered T] [NoMaxOrder T] (s : PointSegmentSignal T)
    (hs : s.IsValid) (h : ∀ t : T, 0 ≤ t → s.at t = false) : -- --- CONCL ---
    ∀ x ∈ s.values, x = false := by -- --- PROOF ---
  have hs' := hs
  obtain ⟨h1, h2, h3, h4, h5⟩ := hs
  intro x hx
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
  have hj' : j < 2 * s.timePoints.length := h2 ▸ hj
  obtain ⟨k, hk, hkj⟩ : ∃ k, k < s.timePoints.length ∧ (j = 2 * k ∨ j = 2 * k + 1) :=
    ⟨j / 2, by omega, by omega⟩
  have ha : s.timePoints[k]? = some s.timePoints[k] := List.getElem?_eq_getElem hk
  -- the value at index `j` is the value at a time point, or between two
  have hnn : 0 ≤ s.timePoints[k] :=
    s.nonneg_of_mem_timePoints hs' _ (List.getElem_mem hk)
  have e : s.values[j] = s.values.getD j false := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  rw [e]
  -- the value at a time point
  rcases hkj with rfl | rfl
  · have := PointSegmentSignal.at_timePoint s hs' k _ ha
    rw [h _ hnn] at this
    simpa [PointSegmentSignal.pointValue, show 2 * (k + 1) - 2 = 2 * k by omega] using this.symm
  · obtain ⟨t, hlt, hub⟩ : ∃ t, s.timePoints[k] < t ∧
        ∀ b, s.timePoints[k + 1]? = some b → t < b := by
      cases hb : s.timePoints[k + 1]? with
      | none => obtain ⟨t, ht⟩ := exists_gt s.timePoints[k]; exact ⟨t, ht, by simp⟩
      | some b =>
        have hlt := List.lt_of_pairwise_getElem_succ h4 ha hb
        obtain ⟨t, ht1, ht2⟩ := exists_between hlt
        exact ⟨t, ht1, by intro b' hb'; simp at hb'; exact hb' ▸ ht2⟩
    have := PointSegmentSignal.at_between s hs' k _ t ha hlt hub
    rw [h t (hnn.trans hlt.le)] at this
    simpa [PointSegmentSignal.succIntervalValue, show 2 * (k + 1) - 1 = 2 * k + 1 by omega]
      using this.symm


-- =======================================  MAIN THEOREM  ======================================= --

theorem PointSegmentSignal.anyTrue_eq_false_of_at {T : Type} [LinearOrder T] [Zero T]
    [DenselyOrdered T] [NoMaxOrder T] (s : PointSegmentSignal T) (hs : s.IsValid)
    (h : ∀ t : T, 0 ≤ t → s.at t = false) (lb : T) (ub : WithTop T) (lc rc : Bool) :
    s.anyTrue lb ub lc rc id = false := by
  have hall := aux_values_false_of_at s hs h
  simp only [PointSegmentSignal.anyTrue, List.any_eq_false]
  intro x hx
  simp [hall x ((List.take_sublist _ _).subset ((List.drop_sublist _ _).subset hx))]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

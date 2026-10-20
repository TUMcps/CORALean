module

public import CORALean.Specification.PointSegmentSignal.Definitions.IsValid
public import CORALean.Specification.PointSegmentSignal.Operations.Basic
public import CORALean.Specification.PointSegmentSignal.Operations.RelevantStart
public import CORALean.Specification.PointSegmentSignal.Theorems.Basic
public import CORALean.Specification.PointSegmentSignal.Theorems.CellBetween
public import CORALean.Specification.PointSegmentSignal.Theorems.CellGeIff
public import CORALean.Specification.PointSegmentSignal.Theorems.CellTimePoint
public import CORALean.Specification.PointSegmentSignal.Theorems.TakeWhileLePos
public import CORALean.Specification.PointSegmentSignal.Theorems.PrecTimeAtValIdxSucc

@[expose] public section

/-!
# The first value an interval reaches

For a valid signal and `lb ≥ 0`, the index `start` of `priv_relevantValueIdx` is one-based, within
`values`, and `start - 1` is the least index a time of the interval reads: every time from `lb` on
(`lb` itself only if the left end is closed) reads at least that index, a closed left end reads
exactly it at `lb`, and an open one at the times just after `lb`.

## Inputs
* `T` – time type
* `s` – signal
* `lb` – interval lower bound
* `lc` – lower bound is closed

## Hypotheses
* `hs` – the signal is valid
* `h0` – the lower bound is nonnegative

## Conclusion
* the start index is in range and lies below the cells the interval reads
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- The first value of an interval is the one read at its left end, or just after it. -/
theorem PointSegmentSignal.relevantStart_spec {T : Type} [LinearOrder T] [Zero T]
    (s : PointSegmentSignal T) (hs : s.IsValid) (lb : T) (h0 : 0 ≤ lb)
    (lc : Bool) : -- --- CONCL ---
    1 ≤ s.relevantStart lb lc ∧ s.relevantStart lb lc ≤ s.values.length ∧
    (∀ t : T, 0 ≤ t → (lb < t ∨ (lc = true ∧ t = lb)) → s.relevantStart lb lc - 1 ≤ s.cell t) ∧
    (lc = true → s.cell lb = s.relevantStart lb lc - 1) ∧
    (lc = false → ∀ t : T, lb < t →
      (∀ b, s.timePoints[(s.timePoints.takeWhile (· ≤ lb)).length]? = some b → t < b) →
        s.cell t = s.relevantStart lb lc - 1) := by -- --- PROOF ---
  have hlen := hs.2.1
  -- the time points at or before `lb`
  obtain ⟨hi1, hi2, ⟨a1, ha1, hale⟩, hnext⟩ := PointSegmentSignal.takeWhile_le_pos s hs lb h0
  have hia : (s.timePoints.takeWhile (· ≤ lb)).length - 1 < s.timePoints.length := by omega
  have ha1' : s.timePoints[(s.timePoints.takeWhile (· ≤ lb)).length - 1] = a1 := by
    rw [List.getElem?_eq_getElem hia] at ha1; exact Option.some.inj ha1
  have hstart : s.relevantStart lb lc = if a1 = lb ∧ lc = true then
      2 * (s.timePoints.takeWhile (· ≤ lb)).length - 1
      else 2 * (s.timePoints.takeWhile (· ≤ lb)).length := by
    simp only [PointSegmentSignal.relevantStart, List.getD_eq_getElem?_getD, ha1, Option.getD_some]
  generalize (s.timePoints.takeWhile (· ≤ lb)).length = i at *
  -- the time point after those `≤ lb`, if there is one, is `> lb`
  have hnx : ∀ h : i - 1 + 1 < s.timePoints.length, lb < s.timePoints[i - 1 + 1] := fun h =>
    hnext _ ((congrArg (fun n => s.timePoints[n]?) (show i = i - 1 + 1 by omega)).trans
      (List.getElem?_eq_getElem h))
  refine ⟨by rw [hstart]; split_ifs <;> omega, by rw [hstart]; split_ifs <;> omega, ?_, ?_, ?_⟩
  · -- every time of the interval reads at least the first value
    intro t ht hlow
    by_cases hcond : a1 = lb ∧ lc = true
    · -- the left end is a closed time point: its point value
      rw [if_pos hcond] at hstart
      rw [hstart]
      have hlo : 2 * i - 1 - 1 < s.values.length := by omega
      refine (s.cell_ge_iff hs t ht _ hlo).2 ?_
      rw [s.precTimeAtValIdx_succ (2 * i - 1 - 1) (by omega)]
      simp only [show (2 * i - 1 - 1) / 2 = i - 1 by omega,
        show (2 * i - 1 - 1) % 2 = 0 by omega, decide_true, true_and, ha1']
      rcases hlow with h | ⟨-, h⟩
      · exact Or.inl (hcond.1 ▸ h)
      · exact Or.inr (hcond.1 ▸ h)
    · -- otherwise the value after the time point `a1`, which is before `t`
      rw [if_neg hcond] at hstart
      rw [hstart]
      have hlo : 2 * i - 1 < s.values.length := by omega
      refine (s.cell_ge_iff hs t ht _ hlo).2 ?_
      rw [s.precTimeAtValIdx_succ (2 * i - 1) (by omega)]
      simp only [show (2 * i - 1) / 2 = i - 1 by omega, ha1']
      refine Or.inl ?_
      rcases hlow with h | ⟨hl, h⟩
      · exact lt_of_le_of_lt hale h
      · exact h ▸ lt_of_le_of_ne hale (fun e => hcond ⟨e, hl⟩)
  · -- a closed left end reads the value of the time point, or just after it
    intro hl
    by_cases hcond : a1 = lb
    · rw [if_pos ⟨hcond, hl⟩] at hstart
      rw [hstart, ← hcond, ← ha1', s.cell_timePoint hs (i - 1) hia (by rw [ha1', hcond]; exact h0)]
      omega
    · rw [if_neg (fun h => hcond h.1)] at hstart
      rw [hstart]
      have := s.cell_between hs (i - 1) hia lb h0 (by rw [ha1']; exact lt_of_le_of_ne hale hcond)
        (fun h => hnx h)
      omega
  · -- an open left end reads the value just after the time point before it
    intro hl t hlt hnxt
    rw [if_neg (fun h => by simp [hl] at h)] at hstart
    rw [hstart]
    have := s.cell_between hs (i - 1) hia t (h0.trans hlt.le)
      (by rw [ha1']; exact lt_of_le_of_lt hale hlt)
      (fun h => hnxt _ ((congrArg (fun n => s.timePoints[n]?) (show i = i - 1 + 1 by omega)).trans
        (List.getElem?_eq_getElem h)))
    omega

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

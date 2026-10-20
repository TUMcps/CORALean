module

public import CORALean.Specification.PointSegmentSignal.Definitions.IsValid
public import CORALean.Specification.PointSegmentSignal.Operations.Cell
public import CORALean.Specification.PointSegmentSignal.Theorems.Basic
public import CORALean.Specification.PointSegmentSignal.Theorems.CellGeIff
public import CORALean.Specification.PointSegmentSignal.Theorems.CellLeIff
public import CORALean.Specification.PointSegmentSignal.Theorems.NonnegOfMemTimePoints
public import Mathlib.Order.Interval.Set.Basic
public import CORALean.Specification.PointSegmentSignal.Theorems.PrecTimeAtValIdxSucc
public import CORALean.Specification.PointSegmentSignal.Theorems.SuccTimeAtValIdxOfLt
public import CORALean.Specification.PointSegmentSignal.Theorems.SuccTimeAtValIdxOfGe
public import CORALean.Specification.PointSegmentSignal.Operations.SuccTimeAtValIdx

@[expose] public section

/-!
# Every stored value is read at some time

In dense time without a last moment, every index of `values` is `cell t` for some `t ≥ 0`: the point
values at the time points, the interval values at a time between two points or after the last.

## Inputs
* `T` – time type
* `s` – signal
* `m` – value index

## Hypotheses
* `hs` – the signal is valid
* `hm` – the index is in range

## Conclusion
* some nonnegative time reads that value
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every value of a valid signal is read at some time. -/
theorem PointSegmentSignal.exists_cell_eq {T : Type} [LinearOrder T] [Zero T] [DenselyOrdered T]
    [NoMaxOrder T] (s : PointSegmentSignal T) (hs : s.IsValid) (m : ℕ) (hm : m < s.values.length) :
    ∃ t, 0 ≤ t ∧ s.cell t = m := by -- --- PROOF ---
  have hlen := hs.2.1
  have hsort := hs.2.2.2.1
  have hk : m / 2 < s.timePoints.length := by omega
  have hnn := PointSegmentSignal.nonneg_of_mem_timePoints s hs _ (List.getElem_mem hk)
  have hpre := s.precTimeAtValIdx_succ m hk
  rcases Nat.mod_two_eq_zero_or_one m with hm0 | hm1
  · -- an even index is the point value of a time point
    have hm2 : (m + 1) / 2 = m / 2 := by omega
    have hsucc := s.succTimeAtValIdx_of_lt m (by omega)
    refine ⟨s.timePoints[m / 2], hnn, le_antisymm ?_ ?_⟩
    · refine (s.cell_le_iff hs _ hnn m hm).2 (Or.inr ⟨?_, ?_⟩) <;> simp [hsucc, hm2, hm0]
    · refine (s.cell_ge_iff hs _ hnn m hm).2 (Or.inr ⟨?_, ?_⟩) <;> simp [hpre, hm0]
  · -- an odd index is the interval value after a time point: a time between it and the next
    obtain ⟨t, hlt, hub⟩ : ∃ t, s.timePoints[m / 2] < t ∧
        (∀ h : m / 2 + 1 < s.timePoints.length, t < s.timePoints[m / 2 + 1]) := by
      by_cases hk2 : m / 2 + 1 < s.timePoints.length
      · have hlt := List.pairwise_iff_getElem.1 hsort (m / 2) (m / 2 + 1) hk hk2 (by omega)
        obtain ⟨t, ht1, ht2⟩ := exists_between hlt
        exact ⟨t, ht1, fun _ => ht2⟩
      · obtain ⟨t, ht⟩ := exists_gt s.timePoints[m / 2]
        exact ⟨t, ht, fun h => absurd h hk2⟩
    have ht0 : 0 ≤ t := hnn.trans hlt.le
    have hm2 : (m + 1) / 2 = m / 2 + 1 := by omega
    refine ⟨t, ht0, le_antisymm ?_ ?_⟩
    · refine (s.cell_le_iff hs _ ht0 m hm).2 (Or.inl ?_)
      by_cases hk2 : m / 2 + 1 < s.timePoints.length
      · rw [s.succTimeAtValIdx_of_lt m (by omega)]
        simpa [hm2] using hub hk2
      · rw [s.succTimeAtValIdx_of_ge m (by omega)]
        exact WithTop.coe_lt_top _
    · refine (s.cell_ge_iff hs _ ht0 m hm).2 (Or.inl ?_)
      simpa [hpre] using hlt

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

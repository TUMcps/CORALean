module

public import CORALean.Specification.PointSegmentSignal.Definitions.IsValid
public import CORALean.Specification.PointSegmentSignal.Operations.Cell
public import CORALean.Specification.PointSegmentSignal.Theorems.TakeWhileLePos
public import Mathlib.Order.Basic

@[expose] public section

/-!
# Where a time lies among the time points

For a valid signal and `t ≥ 0`, `p` time points are `≤ t`, the last one `a0`, and `cell t` is `2 (p
- 1)` if `a0 = t` and `2 (p - 1) + 1` otherwise. Time point `j` is `≤ t` if `j < p`, `> t` if `p ≤
j`, and `< t` if `j + 1 < p`; it is `a0` if `j + 1 = p`.

## Inputs
* `T` – time type
* `s` – signal
* `t` – time
* `j` – time point index

## Hypotheses
* `hs` – the signal is valid
* `ht` – the time is nonnegative
* `hj` – the index is in range

## Conclusion
* the cell is determined by the time points at or before the time
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The position data of `t`. -/
theorem aux_cell_data {T : Type} [LinearOrder T] [Zero T] (s : PointSegmentSignal T)
    (hs : s.IsValid) (t : T) (ht : 0 ≤ t) : -- --- CONCL ---
    ∃ p a, 1 ≤ p ∧ p ≤ s.timePoints.length ∧ s.timePoints[p - 1]? = some a ∧ a ≤ t ∧
      (∀ b, s.timePoints[p]? = some b → t < b) ∧
      s.cell t = (if a = t then 2 * (p - 1) else 2 * (p - 1) + 1) ∧
      p = (s.timePoints.takeWhile (· ≤ t)).length := by -- --- PROOF ---
  obtain ⟨h1, h2, ⟨a, ha, hale⟩, hnext⟩ := PointSegmentSignal.takeWhile_le_pos s hs t ht
  refine ⟨_, a, h1, h2, ha, hale, hnext, ?_, rfl⟩
  unfold PointSegmentSignal.cell
  simp only [ha, Option.some.injEq]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The time points around `t`, and the value `cell t`. -/
theorem PointSegmentSignal.cell_rel {T : Type} [LinearOrder T] [Zero T] (s : PointSegmentSignal T)
    (hs : s.IsValid) (t : T) (ht : 0 ≤ t) (j : ℕ) (hj : j < s.timePoints.length) : -- --- CONCL ---
    ∃ p a0, 1 ≤ p ∧ p ≤ s.timePoints.length ∧
      s.cell t = (if a0 = t then 2 * (p - 1) else 2 * (p - 1) + 1) ∧ a0 ≤ t ∧
      (j + 1 ≤ p → s.timePoints[j] ≤ t) ∧ (p ≤ j → t < s.timePoints[j]) ∧
      (j + 1 < p → s.timePoints[j] < t) ∧ (j + 1 = p → s.timePoints[j] = a0) ∧
      p = (s.timePoints.takeWhile (· ≤ t)).length ∧
        s.timePoints[p - 1]? = some a0 := by -- --- PROOF ---
  obtain ⟨p, a0, hp1, hp2, hpa, hle, hnext, hcell, hpd⟩ := aux_cell_data s hs t ht
  have hsort := hs.2.2.2.1
  have hp2' : p ≤ s.timePoints.length := hp2
  have hp3 : p - 1 < s.timePoints.length := by omega
  have ha0 : s.timePoints[p - 1] = a0 := by
    have hpa' : s.timePoints[p - 1]? = some a0 := hpa
    rw [List.getElem?_eq_getElem hp3] at hpa'; exact Option.some.inj hpa'
  refine ⟨p, a0, hp1, hp2', hcell, hle, ?_, ?_, ?_, ?_, hpd, hpa⟩
  -- at most `t` if `j < p`
  · intro h
    rcases (show j = p - 1 ∨ j < p - 1 by omega) with h' | h'
    · have : s.timePoints[j] = a0 := by rw [← ha0]; congr 1
      rw [this]; exact hle
    · have := List.pairwise_iff_getElem.1 hsort j (p - 1) hj hp3 h'
      rw [ha0] at this
      exact (this.trans_le hle).le
  -- after `t` if `p ≤ j`
  · intro h
    have hp4 : p < s.timePoints.length := lt_of_le_of_lt h hj
    have hb : s.timePoints[p]? = some s.timePoints[p] := List.getElem?_eq_getElem hp4
    have h1 := hnext _ hb
    rcases h.eq_or_lt with h' | h'
    · have : s.timePoints[j] = s.timePoints[p] := by congr 1; omega
      rw [this]; exact h1
    · exact h1.trans (List.pairwise_iff_getElem.1 hsort p j hp4 hj h')
  -- strictly before `t` if `j + 1 < p`
  · intro h
    have := List.pairwise_iff_getElem.1 hsort j (p - 1) hj hp3 (by omega)
    rw [ha0] at this
    exact this.trans_le hle
  · intro h; rw [← ha0]; congr 1; omega

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

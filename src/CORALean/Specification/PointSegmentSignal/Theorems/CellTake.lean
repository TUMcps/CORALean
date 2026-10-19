module

public import CORALean.Specification.PointSegmentSignal.Definitions.IsValid
public import CORALean.Specification.PointSegmentSignal.Operations.Cell
public import CORALean.Specification.PointSegmentSignal.Theorems.CellRel
public import Mathlib.Algebra.Order.Group.Nat

@[expose] public section

/-!
# The stored value a time reads after cutting the time points

Keeping the first `k` time points of a valid signal, with any values, a time `t ≥ 0` reads the same
index as before while that index is among the first `2 k` values, and the last one afterwards.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The points of a prefix that are `≤ t` are a prefix of those of the list. -/
theorem aux_takeWhile_take {α : Type} (p : α → Bool) (l : List α) (k : ℕ) :
    ((l.take k).takeWhile p).length = min (l.takeWhile p).length k := by -- --- PROOF ---
  induction l generalizing k with
  | nil => simp
  | cons x l ih =>
    cases k with
    | zero => simp
    | succ k =>
      by_cases hx : p x = true
      · simp only [List.take_succ_cons, List.takeWhile_cons, hx, if_true, List.length_cons, ih]
        omega
      · simp [hx]


-- =======================================  MAIN THEOREM  ======================================= --

/-- After cutting to the first `k` time points `cell` is capped at the last value. -/
theorem PointSegmentSignal.cell_take {T : Type} [LinearOrder T] [Zero T] (s : PointSegmentSignal T)
    (hs : s.IsValid) (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k ≤ s.timePoints.length) (vals : List Bool)
    (t : T) (ht : 0 ≤ t) : -- --- CONCL ---
    (PointSegmentSignal.mk (s.timePoints.take k) vals).cell t =
      if s.cell t ≤ 2 * k - 1 then s.cell t else 2 * k - 1 := by -- --- PROOF ---
  obtain ⟨p, a0, hp1, hp2, hcell, hle, hx1, hx2, hx3, hx4, hpd, hpa⟩ :=
    s.cell_rel hs t ht 0 (by omega)
  -- the index `s` reads, in terms of the number `p` of points `≤ t`
  rw [hcell]
  unfold PointSegmentSignal.cell
  dsimp only
  rw [aux_takeWhile_take, ← hpd]
  by_cases hpk : p ≤ k
  · -- the last point `≤ t` is kept
    rw [min_eq_left hpk, List.getElem?_take_of_lt (by omega), hpa]
    have hv : (if a0 = t then 2 * (p - 1) else 2 * (p - 1) + 1) ≤ 2 * k - 1 := by
      split_ifs <;> omega
    rw [if_pos hv]
    by_cases hat : a0 = t <;> simp [hat]
  · -- the points are cut before `t`: the last kept point is before it
    have hkn : k < s.timePoints.length := by omega
    rw [min_eq_right (by omega), List.getElem?_take_of_lt (by omega)]
    have hv : ¬ (if a0 = t then 2 * (p - 1) else 2 * (p - 1) + 1) ≤ 2 * k - 1 := by
      split_ifs <;> omega
    rw [if_neg hv]
    obtain ⟨p', a1, -, -, -, -, hy1, -, -, -, hpd', -⟩ := s.cell_rel hs t ht k hkn
    have hlt : s.timePoints[k - 1] < s.timePoints[k] :=
      List.pairwise_iff_getElem.1 hs.2.2.2.1 (k - 1) k (by omega) hkn (by omega)
    have hkt : s.timePoints[k] ≤ t := hy1 (by omega)
    have hne : s.timePoints[k - 1]? ≠ some t := by
      rw [List.getElem?_eq_getElem (by omega)]
      intro h
      have := Option.some.inj h
      exact absurd (this ▸ hlt) (not_lt.2 hkt)
    rw [if_neg hne]
    omega
end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

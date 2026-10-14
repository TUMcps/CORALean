module

public import CORALean.Specification.PointSegmentSignal.Definitions.IsValid
public import CORALean.Specification.PointSegmentSignal.Operations.Basic
public import CORALean.Specification.PointSegmentSignal.Operations.Cell
public import CORALean.Specification.PointSegmentSignal.Theorems.CellRel
public import Mathlib.Order.Basic

@[expose] public section

/-!
# The lower end of a run of values

`a ≤ cell t` iff `t` lies after the time point `precTimeAtValIdx` gives for the `a`-th value
(zero-based), or at it if the value is the point value.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- Index `a ≤ cell t` iff `t` is past the lower end of the `a`-th value. -/
theorem PointSegmentSignal.cell_ge_iff {T : Type} [LinearOrder T] [Zero T]
    (s : PointSegmentSignal T) (hs : s.IsValid) (t : T) (ht : 0 ≤ t) (a : ℕ)
    (ha : a < s.values.length) :
    a ≤ s.cell t ↔ ((s.precTimeAtValIdx (a + 1)).1 < t ∨
      ((s.precTimeAtValIdx (a + 1)).2 = true ∧
        t = (s.precTimeAtValIdx (a + 1)).1)) := by -- --- PROOF ---
  have hlen := hs.2.1
  have hk : a / 2 < s.timePoints.length := by omega
  -- the time point of the `a`-th value, and whether the value is a point value
  have hpre : s.precTimeAtValIdx (a + 1) = (s.timePoints[a / 2], decide (a % 2 = 0)) := by
    simp only [PointSegmentSignal.precTimeAtValIdx]
    rw [show (a + 1 + 1) / 2 - 1 = a / 2 by omega]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
    omega
  rw [hpre]
  simp only [decide_eq_true_eq]
  obtain ⟨p, a0, hp1, hp2, hcell, hle, hx1, hx2, hx3, hx4, -⟩ := s.cell_rel hs t ht (a / 2) hk
  rw [hcell]
  -- compare the position of the `a`-th time point with `p`
  rcases lt_trichotomy (a / 2 + 1) p with c1 | c2 | c3
  · refine iff_of_true ?_ (Or.inl (hx3 c1))
    split_ifs <;> omega
  · have e := hx4 c2
    -- the time point is `t` itself, or before it
    by_cases hd : a0 = t
    · simp only [hd, if_true]
      rw [e, hd]
      constructor
      · intro h; right; exact ⟨by omega, rfl⟩
      · rintro (h | ⟨h, -⟩)
        · exact absurd h (lt_irrefl _)
        · omega
    · simp only [hd, if_false]
      refine iff_of_true (by omega) (Or.inl ?_)
      rw [e]; exact lt_of_le_of_ne hle hd
  -- the time point is after `t`
  · refine iff_of_false ?_ ?_
    · split_ifs <;> omega
    · rintro (h | ⟨-, h⟩)
      · exact absurd (hx2 (by omega)) (not_lt.2 h.le)
      · exact absurd (hx2 (by omega)) (not_lt.2 h.ge)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

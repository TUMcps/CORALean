module

public import CORALean.Specification.PointSegmentSignal.Definitions.IsValid
public import CORALean.Specification.PointSegmentSignal.Operations.Basic
public import CORALean.Specification.PointSegmentSignal.Operations.Cell
public import CORALean.Specification.PointSegmentSignal.Theorems.CellRel
public import Mathlib.Order.Basic
public import CORALean.Specification.PointSegmentSignal.Operations.SuccTimeAtValIdx

@[expose] public section

/-!
# The upper end of a run of values

`cell t ≤ b` iff `t` lies before the time point `succTimeAtValIdx` gives for the `b`-th value
(zero-based, `inf` past the last point), or at it if the value is the point value.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- Index `cell t ≤ b` iff `t` is before the upper end of the `b`-th value. -/
theorem PointSegmentSignal.cell_le_iff {T : Type} [LinearOrder T] [Zero T]
    (s : PointSegmentSignal T) (hs : s.IsValid) (t : T) (ht : 0 ≤ t) (b : ℕ)
    (hb : b < s.values.length) : -- --- STMT ---
    s.cell t ≤ b ↔ (((t : T) : WithTop T) < (s.succTimeAtValIdx (b + 1)).1 ∨
      ((s.succTimeAtValIdx (b + 1)).2 = true ∧
        ((t : T) : WithTop T) = (s.succTimeAtValIdx (b + 1)).1)) := by -- --- PROOF ---
  have hlen := hs.2.1
  have hsucc : s.succTimeAtValIdx (b + 1) = (if (b + 1) / 2 + 1 > s.timePoints.length then ⊤
      else (((s.timePoints.getD ((b + 1) / 2) 0 : T)) : WithTop T), decide (b % 2 = 0)) := by
    simp only [PointSegmentSignal.succTimeAtValIdx, PointSegmentSignal.length]
    exact Prod.ext rfl (decide_eq_decide.2 (by omega))
  rw [hsucc]
  simp only [decide_eq_true_eq]
  by_cases hj : (b + 1) / 2 < s.timePoints.length
  · -- the upper end is a time point
    rw [if_neg (by omega), List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj,
      Option.getD_some]
    simp only [WithTop.coe_lt_coe, WithTop.coe_inj]
    obtain ⟨p, a0, hp1, hp2, hcell, hle, hx1, hx2, hx3, hx4, -⟩ :=
      s.cell_rel hs t ht ((b + 1) / 2) hj
    rw [hcell]
    -- compare the position of that time point with `p`
    rcases lt_trichotomy ((b + 1) / 2 + 1) p with c1 | c2 | c3
    · refine iff_of_false ?_ ?_
      · split_ifs <;> omega
      · rintro (h | ⟨-, h⟩)
        · exact absurd (hx3 c1) (not_lt.2 h.le)
        · exact absurd (hx3 c1) (not_lt.2 h.le)
    · have e := hx4 c2
      rw [e]
      -- the time point is `t` itself, or before it
      by_cases hd : a0 = t
      · simp only [hd, if_true]
        constructor
        · intro h
          right; exact ⟨by omega, trivial⟩
        · rintro (h | ⟨h, -⟩)
          · exact absurd h (lt_irrefl _)
          · omega
      · simp only [hd, if_false]
        refine iff_of_false (by omega) ?_
        rintro (h | ⟨-, h⟩)
        · exact absurd h (not_lt.2 hle)
        · exact hd h.symm
    -- the time point is after `t`
    · refine iff_of_true ?_ (Or.inl (hx2 (by omega)))
      split_ifs <;> omega
  · -- the upper end is `inf`
    rw [if_pos (by omega)]
    refine iff_of_true ?_ (Or.inl (WithTop.coe_lt_top _))
    obtain ⟨p, a0, hp1, hp2, hcell, hle, -⟩ := s.cell_rel hs t ht 0 (by omega)
    rw [hcell]
    split_ifs <;> omega

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

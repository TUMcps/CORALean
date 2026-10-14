module

public import CORALean.Specification.PointSegmentSignal.Definitions.IsValid
public import CORALean.Specification.PointSegmentSignal.Operations.Basic
public import CORALean.Specification.PointSegmentSignal.Operations.Cell
public import CORALean.Specification.PointSegmentSignal.Theorems.CellRel
public import Mathlib.Order.Basic

@[expose] public section

/-!
# The stored value a time reads exists

For a valid signal and `t ≥ 0`, `cell t` is an index into `values`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- `cell t` is an index of `values`. -/
theorem PointSegmentSignal.cell_lt {T : Type} [LinearOrder T] [Zero T] (s : PointSegmentSignal T)
    (hs : s.IsValid) (t : T) (ht : 0 ≤ t) : s.cell t < s.values.length := by
  obtain ⟨p, a0, hp1, hp2, hcell, -⟩ := s.cell_rel hs t ht 0 (List.length_pos_iff.2 hs.1)
  have := hs.2.1
  rw [hcell]
  split_ifs <;> omega

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

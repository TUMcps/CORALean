module

public import CORALean.Specification.PointSegmentSignal.Definitions.IsValid
public import CORALean.Specification.PointSegmentSignal.Theorems.Basic
public import CORALean.Specification.PointSegmentSignal.Theorems.CellGeIff
public import CORALean.Specification.PointSegmentSignal.Theorems.CellLeIff
public import CORALean.Specification.PointSegmentSignal.Theorems.PrecTimeAtValIdxSucc
public import CORALean.Specification.PointSegmentSignal.Theorems.SuccTimeAtValIdxOfLt
public import CORALean.Specification.PointSegmentSignal.Operations.SuccTimeAtValIdx

@[expose] public section

/-!
# The stored value a time point reads

The `k`-th time point of a valid signal reads the point value `2 k`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- The point value of the `k`-th time point. -/
theorem PointSegmentSignal.cell_timePoint {T : Type} [LinearOrder T] [Zero T]
    (s : PointSegmentSignal T) (hs : s.IsValid) (k : ℕ) (hk : k < s.timePoints.length)
    (h0 : 0 ≤ s.timePoints[k]) : s.cell s.timePoints[k] = 2 * k := by -- --- PROOF ---
  have hlen := hs.2.1
  have hb : 2 * k < s.values.length := by omega
  have hk' : (2 * k) / 2 < s.timePoints.length := by omega
  have hpre := s.precTimeAtValIdx_succ (2 * k) (by omega)
  have hsucc := s.succTimeAtValIdx_of_lt (2 * k) (by omega)
  refine le_antisymm ?_ ?_
  · refine (s.cell_le_iff hs _ h0 (2 * k) hb).2 (Or.inr ⟨?_, ?_⟩)
    · simp [hsucc]
    · simp [hsucc]
      congr 1
      omega
  · refine (s.cell_ge_iff hs _ h0 (2 * k) hb).2 (Or.inr ⟨?_, ?_⟩)
    · simp [hpre]
    · simp [hpre]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

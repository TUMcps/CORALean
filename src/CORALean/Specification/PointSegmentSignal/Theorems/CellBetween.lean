module

public import CORALean.Specification.PointSegmentSignal.Definitions.IsValid
public import CORALean.Specification.PointSegmentSignal.Theorems.Basic
public import CORALean.Specification.PointSegmentSignal.Theorems.CellGeIff
public import CORALean.Specification.PointSegmentSignal.Theorems.CellLeIff
public import CORALean.Specification.PointSegmentSignal.Theorems.PrecTimeAtValIdxSucc
public import CORALean.Specification.PointSegmentSignal.Theorems.SuccTimeAtValIdxOfLt
public import CORALean.Specification.PointSegmentSignal.Theorems.SuccTimeAtValIdxOfGe
public import CORALean.Specification.PointSegmentSignal.Operations.SuccTimeAtValIdx

@[expose] public section

/-!
# The stored value a time between two time points reads

A time after the `k`-th time point and before the next one, if there is one, reads the interval
value `2 k + 1`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- The interval value after the `k`-th time point. -/
theorem PointSegmentSignal.cell_between {T : Type} [LinearOrder T] [Zero T]
    (s : PointSegmentSignal T) (hs : s.IsValid) (k : ℕ) (hk : k < s.timePoints.length) (t : T)
    (h0 : 0 ≤ t) (h1 : s.timePoints[k] < t)
    (h2 : ∀ h : k + 1 < s.timePoints.length, t < s.timePoints[k + 1]) :
    s.cell t = 2 * k + 1 := by -- --- PROOF ---
  have hlen := hs.2.1
  have hb : 2 * k + 1 < s.values.length := by omega
  have hpre := s.precTimeAtValIdx_succ (2 * k + 1) (by omega)
  refine le_antisymm ?_ ?_
  · refine (s.cell_le_iff hs _ h0 (2 * k + 1) hb).2 (Or.inl ?_)
    by_cases hk2 : k + 1 < s.timePoints.length
    · rw [s.succTimeAtValIdx_of_lt (2 * k + 1) (by omega)]
      simpa [show (2 * k + 1 + 1) / 2 = k + 1 by omega] using h2 hk2
    · rw [s.succTimeAtValIdx_of_ge (2 * k + 1) (by omega)]
      exact WithTop.coe_lt_top _
  · refine (s.cell_ge_iff hs _ h0 (2 * k + 1) hb).2 (Or.inl ?_)
    simpa [hpre, show (2 * k + 1) / 2 = k by omega] using h1

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

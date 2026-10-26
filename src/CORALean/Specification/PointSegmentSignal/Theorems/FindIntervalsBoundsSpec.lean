module

public import CORALean.Specification.PointSegmentSignal.Theorems.Basic
public import CORALean.Specification.PointSegmentSignal.Theorems.CellLt
public import CORALean.Specification.PointSegmentSignal.Theorems.CellMemBounds
public import CORALean.Specification.PointSegmentSignal.Theorems.FindIntervalsBoundsRuns
public import CORALean.Specification.PointSegmentSignal.Theorems.NonnegOfMemTimePoints
public import CORALean.Specification.STLInterval.Definitions.IsInBounds
public import CORALean.Specification.PointSegmentSignal.Theorems.AtEqCell

@[expose] public section

/-!
# `findIntervals` covers the times where the condition holds

For a valid signal, the intervals of `findIntervals(obj,cond)` have lower bounds `≥ 0`, and a time
`t ≥ 0` lies in one of them exactly when `cond` holds of the value the signal has at `t`.

## Inputs
* `T` – time type
* `s` – signal
* `cond` – condition on values

## Hypotheses
* `hs` – the signal is valid

## Conclusion
* the intervals start nonnegative and cover the times where the condition holds
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A time point, or the default, is `≥ 0`. -/
private theorem aux_getD_nonneg {T : Type} [LinearOrder T] [Zero T] (s : PointSegmentSignal T)
    (hs : s.IsValid) (i : ℕ) : 0 ≤ s.timePoints.getD i 0 := by
  rcases lt_or_ge i s.timePoints.length with h | h
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]
    exact PointSegmentSignal.nonneg_of_mem_timePoints s hs _ (List.getElem_mem h)
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h, Option.getD_none]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The intervals of `findIntervals` are exactly the times at which `cond` holds. -/
theorem PointSegmentSignal.findIntervalsBounds_spec {T : Type} [LinearOrder T] [Zero T]
    (s : PointSegmentSignal T) (hs : s.IsValid) (cond : Bool → Bool) : -- --- CONCL ---
    (∀ b ∈ s.findIntervalsBounds cond, 0 ≤ b.1) ∧ ∀ t : T, 0 ≤ t →
      ((∃ b ∈ s.findIntervalsBounds cond,
        STLInterval.IsInBounds b.1 b.2.1 b.2.2.1 b.2.2.2 t) ↔
          cond (s.at t) = true) := by -- --- PROOF ---
  obtain ⟨runs, heq, hT1, hT2⟩ := s.findIntervalsBounds_runs hs cond
  rw [heq]
  refine ⟨?_, ?_⟩
  · -- every lower bound is a time point, or the point `0`
    intro b hb
    rw [List.mem_map] at hb
    obtain ⟨p, hp, rfl⟩ := hb
    exact aux_getD_nonneg s hs _
  · intro t ht
    have hct := s.cell_lt hs t ht
    rw [PointSegmentSignal.at_eq_cell]
    simp only [List.mem_map, Prod.exists]
    constructor
    · -- a time in a run reads a value of the run
      rintro ⟨a, a1, a2, b, ⟨r, f, hp, hEq⟩, hb⟩
      simp only [Prod.mk.injEq] at hEq
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hEq
      obtain ⟨h1, h2, h3, h4, -⟩ := hT1 (r, f) hp
      simp only at h1 h2 h3 h4
      rw [s.cell_mem_bounds hs r f h1 (by omega) (by omega) (by omega) t ht] at hb
      have := h4 (s.cell t + 1) (by omega) (by omega)
      simpa using this
    · -- a value that satisfies `cond` lies in a run
      intro h
      obtain ⟨⟨r, f⟩, hp, h1, h2⟩ := hT2 (s.cell t + 1) (by omega) (by omega) (by simpa using h)
      obtain ⟨g1, g2, g3, -⟩ := hT1 (r, f) hp
      simp only at g1 g2 g3 h1 h2
      refine ⟨_, _, _, _, ⟨r, f, hp, rfl⟩, ?_⟩
      rw [s.cell_mem_bounds hs r f g1 (by omega) (by omega) (by omega) t ht]
      omega

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

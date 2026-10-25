module

public import CORALean.Specification.PointSegmentSignal.Operations.FindIntervals
public import CORALean.Specification.PointSegmentSignal.Theorems.Basic
public import CORALean.Specification.PointSegmentSignal.Theorems.CellMemBounds
public import CORALean.Specification.PointSegmentSignal.Theorems.CellMono
public import CORALean.Specification.PointSegmentSignal.Theorems.ExistsCellEq
public import Mathlib.Order.Interval.Set.Basic
public import CORALean.Specification.PointSegmentSignal.Theorems.AtEqCell
public import CORALean.Specification.PointSegmentSignal.Theorems.FindIntervalsBoundsSpec
public import CORALean.Specification.STLInterval.Definitions.IsMaximalRuns
public import CORALean.Specification.STLInterval.Theorems.SetStlIntervalBounds

@[expose] public section

/-!
# `findIntervals` returns the maximal intervals where the condition holds

For a valid signal over `ℝ`, the intervals of `findIntervals(obj,cond)` start at times `≥ 0`, a time
`t ≥ 0` is in one of them exactly when `cond` holds of the value of the signal at `t`, and an
interval cannot be extended: a time reached from it through times that all satisfy `cond` is in it.

## Inputs
* `s` – signal
* `cond` – condition on values

## Hypotheses
* `hs` – the signal is valid

## Conclusion
* the intervals are the maximal intervals where the condition holds
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A time reached from an interval through times satisfying `cond` is in the interval. -/
theorem PointSegmentSignal.aux_findIntervalsBounds_maximal {T : Type} [LinearOrder T] [Zero T]
    [DenselyOrdered T] [NoMaxOrder T] (s : PointSegmentSignal T) (hs : s.IsValid)
    (cond : Bool → Bool) (b : T × WithTop T × Bool × Bool) (hb : b ∈ s.findIntervalsBounds cond)
    (t₁ t₂ : T) (ht₂ : 0 ≤ t₂) (h₁ : STLInterval.IsInBounds b.1 b.2.1 b.2.2.1 b.2.2.2 t₁)
    (hpath : ∀ t, 0 ≤ t → min t₁ t₂ ≤ t → t ≤ max t₁ t₂ → cond (s.at t) = true) : -- --- CONCL ---
    STLInterval.IsInBounds b.1 b.2.1 b.2.2.1 b.2.2.2 t₂ := by -- --- PROOF ---
  obtain ⟨runs, heq, hT1, -⟩ := s.findIntervalsBounds_runs hs cond
  rw [heq, List.mem_map] at hb
  obtain ⟨⟨r, f⟩, hp, rfl⟩ := hb
  obtain ⟨g1, g2, g3, g4, g5, g6⟩ := hT1 (r, f) hp
  simp only at g1 g2 g3 g4 g5 g6 h₁ ⊢
  -- the lower bound is `≥ 0`, so `t₁ ≥ 0`
  have ht₁ : 0 ≤ t₁ := by
    have h0 := (s.findIntervalsBounds_spec hs cond).1
    refine le_trans (h0 _ (by rw [heq]; exact List.mem_map.2 ⟨(r, f), hp, rfl⟩)) ?_
    rcases h₁.1 with h | ⟨-, h⟩
    · exact h.le
    · exact h.ge
  have hN := s.cell_lt hs t₂ ht₂
  rw [s.cell_mem_bounds hs r f g1 (by omega) (by omega) (by omega) t₁ ht₁] at h₁
  rw [s.cell_mem_bounds hs r f g1 (by omega) (by omega) (by omega) t₂ ht₂]
  -- a time reading a value outside the run, between `t₁` and `t₂`, would break the path
  refine ⟨?_, ?_⟩
  · by_contra hlt
    -- `t₂` reads a value before the run: take a time reading the value just before it
    obtain ⟨t, ht0, hct, hte⟩ : ∃ t, 0 ≤ t ∧ s.cell t = r - 2 ∧ (s.cell t₂ = r - 2 → t = t₂) := by
      by_cases he : s.cell t₂ = r - 2
      · exact ⟨t₂, ht₂, he, fun _ => rfl⟩
      · obtain ⟨t, h0, hc⟩ := s.exists_cell_eq hs (r - 2) (by omega)
        exact ⟨t, h0, hc, fun h => absurd h he⟩
    have h1 : t ≤ t₁ := by
      by_contra h; have := s.cell_mono hs t₁ t ht₁ (not_le.1 h).le; omega
    have h2 : t₂ ≤ t := by
      by_cases he : s.cell t₂ = r - 2
      · exact (hte he).ge
      · by_contra h; have := s.cell_mono hs t t₂ ht0 (not_le.1 h).le; omega
    have := hpath t ht0 ((min_le_right _ _).trans h2) (h1.trans (le_max_left _ _))
    rw [PointSegmentSignal.at_eq_cell, hct, g5 (by omega)] at this
    exact absurd this (by simp)
  · by_contra hlt
    -- `t₂` reads a value after the run: take a time reading the value just after it
    obtain ⟨t, ht0, hct, hte⟩ : ∃ t, 0 ≤ t ∧ s.cell t = f ∧ (s.cell t₂ = f → t = t₂) := by
      by_cases he : s.cell t₂ = f
      · exact ⟨t₂, ht₂, he, fun _ => rfl⟩
      · obtain ⟨t, h0, hc⟩ := s.exists_cell_eq hs f (by omega)
        exact ⟨t, h0, hc, fun h => absurd h he⟩
    have h1 : t₁ ≤ t := by
      by_contra h; have := s.cell_mono hs t t₁ ht0 (not_le.1 h).le; omega
    have h2 : t ≤ t₂ := by
      by_cases he : s.cell t₂ = f
      · exact (hte he).le
      · by_contra h; have := s.cell_mono hs t₂ t ht₂ (not_le.1 h).le; omega
    have := hpath t ht0 ((min_le_left _ _).trans h1) (h2.trans (le_max_right _ _))
    rw [PointSegmentSignal.at_eq_cell, hct, g6 (by omega)] at this
    exact absurd this (by simp)


-- =======================================  MAIN THEOREM  ======================================= --

/-- The intervals of `findIntervals` are the maximal intervals at which `cond` holds. -/
theorem PointSegmentSignal.findIntervals_spec (s : PointSegmentSignal ℝ) (hs : s.IsValid)
    (cond : Bool → Bool) : -- --- CONCL ---
    STLInterval.IsMaximalRuns (s.findIntervals cond)
      (fun t => cond (s.at t) = true) := by -- --- PROOF ---
  unfold STLInterval.IsMaximalRuns
  obtain ⟨h0, h1⟩ := s.findIntervalsBounds_spec hs cond
  refine ⟨fun t ht => ?_, ?_⟩
  · show _ ↔ cond (s.at t) = true
    rw [← h1 t ht]
    constructor
    · rintro ⟨I, hI, hmem⟩
      obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hI
      exact ⟨b, hb, (STLInterval.mem_set_stlIntervalBounds _ _ _ _ (h0 b hb) _).1 hmem⟩
    · rintro ⟨b, hb, hmem⟩
      exact ⟨_, List.mem_map.2 ⟨b, hb, rfl⟩,
        (STLInterval.mem_set_stlIntervalBounds _ _ _ _ (h0 b hb) _).2 hmem⟩
  · intro I hI t₁ ht₁ t₂ ht₂ hpath
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hI
    rw [STLInterval.mem_set_stlIntervalBounds _ _ _ _ (h0 b hb)] at ht₁ ⊢
    exact s.aux_findIntervalsBounds_maximal hs cond b hb t₁ t₂ ht₂ ht₁ hpath

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

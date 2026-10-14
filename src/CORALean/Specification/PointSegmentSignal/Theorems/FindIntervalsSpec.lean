module

public import CORALean.Specification.PointSegmentSignal.Operations.FindIntervals
public import CORALean.Specification.PointSegmentSignal.Theorems.FindIntervalsBoundsMaximal
public import CORALean.Specification.PointSegmentSignal.Theorems.FindIntervalsBoundsSpec
public import CORALean.Specification.STLInterval.Definitions.MaximalRuns
public import CORALean.Specification.STLInterval.Theorems.FieldsStlIntervalBounds
public import CORALean.Specification.STLInterval.Theorems.SetStlIntervalBounds

@[expose] public section

/-!
# `findIntervals` returns the maximal intervals where the condition holds

For a valid signal over `ℝ`, the intervals of `findIntervals(obj,cond)` start at times `≥ 0`, a time
`t ≥ 0` is in one of them exactly when `cond` holds of the value of the signal at `t`, and an
interval cannot be extended: a time reached from it through times that all satisfy `cond` is in it.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- The intervals of `findIntervals` are the maximal intervals at which `cond` holds. -/
theorem PointSegmentSignal.findIntervals_spec (s : PointSegmentSignal ℝ) (hs : s.IsValid)
    (cond : Bool → Bool) :
    STLInterval.MaximalRuns (s.findIntervals cond)
      (fun t => cond (s.at t) = true) := by -- --- PROOF ---
  unfold STLInterval.MaximalRuns
  obtain ⟨h0, h1⟩ := s.findIntervalsBounds_spec hs cond
  refine ⟨?_, fun t ht => ?_, ?_⟩
  · -- the lower bounds are those of `findIntervalsBounds`
    intro I hI
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hI
    exact STLInterval.fields_stlIntervalBounds _ _ _ _ (h0 b hb)
  · show _ ↔ cond (s.at t) = true
    rw [← h1 t ht]
    constructor
    · rintro ⟨I, hI, hmem⟩
      obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hI
      exact ⟨b, hb, (STLInterval.mem_set_stlIntervalBounds _ _ _ _ _).1 hmem⟩
    · rintro ⟨b, hb, hmem⟩
      exact ⟨_, List.mem_map.2 ⟨b, hb, rfl⟩,
        (STLInterval.mem_set_stlIntervalBounds _ _ _ _ _).2 hmem⟩
  · intro I hI t₁ ht₁ t₂ ht₂ hpath
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hI
    rw [STLInterval.mem_set_stlIntervalBounds] at ht₁ ⊢
    exact s.findIntervalsBounds_maximal hs cond b hb t₁ t₂ ht₂ ht₁ hpath

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

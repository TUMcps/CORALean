module

public import CORALean.Specification.PointSegmentSignal.Operations.FindIntervals
public import CORALean.Specification.PointSegmentSignal.Theorems.FindIntervalsBoundsMaximal
public import CORALean.Specification.PointSegmentSignal.Theorems.FindIntervalsBoundsSpec
public import CORALean.Specification.STLInterval.Definitions.MaximalRuns
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


-- =======================================  MAIN THEOREM  ======================================= --

/-- The intervals of `findIntervals` are the maximal intervals at which `cond` holds. -/
theorem PointSegmentSignal.findIntervals_spec (s : PointSegmentSignal ℝ) (hs : s.IsValid)
    (cond : Bool → Bool) : -- --- CONCL ---
    STLInterval.MaximalRuns (s.findIntervals cond)
      (fun t => cond (s.at t) = true) := by -- --- PROOF ---
  unfold STLInterval.MaximalRuns
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
    exact s.findIntervalsBounds_maximal hs cond b hb t₁ t₂ ht₂ ht₁ hpath

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

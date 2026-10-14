module

public import CORALean.Specification.PointSegmentSignal.Definitions.IsValid
public import CORALean.Specification.PointSegmentSignal.Operations.Basic
public import CORALean.Specification.PointSegmentSignal.Theorems.Basic

@[expose] public section

/-!
# Negation keeps a signal valid

`~obj` of a valid signal is valid: the time points are those of `obj`, and a point is redundant
in `~obj` exactly when it is in `obj`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem PointSegmentSignal.not_isValid {T : Type} [LinearOrder T] [Zero T]
    (s : PointSegmentSignal T) (hs : s.IsValid) : s.not.IsValid := by -- --- PROOF ---
  obtain ⟨h1, h2, h3, h4, h5⟩ := hs
  refine ⟨h1, by simpa [PointSegmentSignal.not] using h2, h3, h4, ?_⟩
  intro i hi hi'
  simp only [PointSegmentSignal.not] at hi' ⊢
  have := h5 i hi hi'
  rw [List.getD_map_not _ _ (by omega), List.getD_map_not _ _ (by omega),
    List.getD_map_not _ _ (by omega)]
  simpa using this

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

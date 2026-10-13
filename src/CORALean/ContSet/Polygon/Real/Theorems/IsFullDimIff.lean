import CORALean.ContSet.Polygon.Real.Operations.IsFullDim
import CORALean.ContSet.VPolytope.Real.Theorems.IsFullDimIff
import CORALean.ContSet.VPolytope.Real.Instances

/-!
# `Polygon.isFullDim` is the nonempty interior

Exactly, for the region: a finite union of closed sets has an interior point iff one of them has
(a closed set with empty interior can be dropped from a union without changing its interior).
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

theorem Polygon.aux_interior_union (s t : Set (Vec ℝ 2)) (hs : IsClosed s) :
    (interior (s ∪ t)).Nonempty ↔
      (interior s).Nonempty ∨ (interior t).Nonempty := by -- --- PROOF ---
  constructor
  · intro h
    by_contra hc
    push Not at hc
    rw [interior_union_isClosed_of_interior_empty hs hc.2, hc.1] at h
    exact Set.not_nonempty_empty h
  · rintro (h | h)
    · exact h.mono (interior_mono Set.subset_union_left)
    · exact h.mono (interior_mono Set.subset_union_right)

theorem Polygon.aux_interior_nonempty_iff (l : List (VPolytope (Vec ℝ 2))) :
    (interior (⋃ p ∈ l, VPolytope.construct p)).Nonempty ↔
      ∃ p ∈ l, (interior (VPolytope.construct p)).Nonempty := by -- --- PROOF ---
  induction l with
  | nil => simp
  | cons a l ih =>
    have e : (⋃ p ∈ a :: l, VPolytope.construct p)
        = VPolytope.construct a ∪ ⋃ p ∈ l, VPolytope.construct p := by simp
    rw [e, Polygon.aux_interior_union _ _ (VPolytope.isCompact_construct a).isClosed, ih]
    simp


-- =======================================  MAIN THEOREM  ======================================= --

/-- A polygon has an interior point iff some piece has affinely spanning vertices. -/
theorem Polygon.isFullDim_iff (P : Polygon) :
    (interior (ContSet.construct P)).Nonempty ↔ Polygon.isFullDim P := by
  change (interior (⋃ s ∈ P.sets, VPolytope.construct s)).Nonempty ↔ _
  unfold Polygon.isFullDim
  rw [Polygon.aux_interior_nonempty_iff]
  simp only [VPolytope.isFullDim_iff]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

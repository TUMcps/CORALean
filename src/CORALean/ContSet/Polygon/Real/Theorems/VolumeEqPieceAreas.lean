module

public import CORALean.ContSet.Polygon.Real.Operations.Volume
public import CORALean.ContSet.Polygon.Real.Operations.PieceAreas
public import CORALean.ContSet.Polygon.Real.Theorems.VolumeLePieceAreas
public import CORALean.ContSet.VPolytope.Real.Theorems.Basic

@[expose] public section

/-!
# `Polygon.volume` equals the piece areas for null-overlapping pieces

The area of the region is at most the sum of the piece areas, and equal to it when the pieces are
pairwise almost-everywhere disjoint (interior-disjoint pieces qualify: a polytope's boundary is
null, which is not used here, the hypothesis is stated on the measure).
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

theorem Polygon.aux_union_eq (l : List (VPolytope (Vec ℝ 2)))
    (h : l.Pairwise fun p q =>
      MeasureTheory.AEDisjoint MeasureTheory.volume
        (VPolytope.construct p) (VPolytope.construct q)) :
    MeasureTheory.volume (⋃ p ∈ l, VPolytope.construct p) =
      (l.map fun p => MeasureTheory.volume (VPolytope.construct p)).sum := by -- --- PROOF ---
  induction l with
  | nil => simp
  | cons a l ih =>
    have e : (⋃ p ∈ a :: l, VPolytope.construct p)
        = VPolytope.construct a ∪ ⋃ p ∈ l, VPolytope.construct p := by simp
    rw [List.pairwise_cons] at h
    have hm : MeasureTheory.NullMeasurableSet (⋃ p ∈ l, VPolytope.construct p) := by
      refine (Set.Finite.isClosed_biUnion l.finite_toSet fun p _ => ?_)
        |>.measurableSet.nullMeasurableSet
      exact (VPolytope.isCompact_construct p).isClosed
    have hd : MeasureTheory.AEDisjoint MeasureTheory.volume (VPolytope.construct a)
        (⋃ p ∈ l, VPolytope.construct p) := by
      unfold MeasureTheory.AEDisjoint
      rw [Set.inter_iUnion₂]
      exact (MeasureTheory.measure_biUnion_null_iff l.finite_toSet.countable).2 fun p hp => h.1 p hp
    rw [e, List.map_cons, List.sum_cons, MeasureTheory.measure_union₀ hm hd, ih h.2]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Exact when the pieces overlap in null sets only. -/
theorem Polygon.volume_eq_pieceAreas (P : Polygon)
    (h : P.sets.Pairwise fun p q => MeasureTheory.AEDisjoint MeasureTheory.volume
      (VPolytope.construct p) (VPolytope.construct q)) :
    Polygon.volume P = Polygon.pieceAreas P :=
  Polygon.aux_union_eq P.sets h

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

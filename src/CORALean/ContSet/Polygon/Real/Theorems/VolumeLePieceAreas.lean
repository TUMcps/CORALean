module

public import CORALean.ContSet.Polygon.Real.Operations.Volume
public import CORALean.ContSet.Polygon.Real.Operations.PieceAreas
public import CORALean.ContSet.VPolytope.Real.Theorems.Basic

@[expose] public section

/-!
# `Polygon.volume` against the piece areas

The area of the region is at most the sum of the piece areas, and equal to it when the pieces are
pairwise almost-everywhere disjoint (`Polygon.volume_eq_pieceAreas`).

## Inputs
* `P` – polygon

## Hypotheses
* none

## Conclusion
* the volume of `P` is at most the sum of its piece areas
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

private theorem Polygon.aux_union_le (l : List (VPolytope (Vec ℝ 2))) : -- --- CONCL ---
    MeasureTheory.volume (⋃ p ∈ l, VPolytope.construct p) ≤
      (l.map fun p => MeasureTheory.volume (VPolytope.construct p)).sum := by -- --- PROOF ---
  induction l with
  | nil => simp
  | cons a l ih =>
    have e : (⋃ p ∈ a :: l, VPolytope.construct p)
        = VPolytope.construct a ∪ ⋃ p ∈ l, VPolytope.construct p := by simp
    rw [e, List.map_cons, List.sum_cons]
    exact (MeasureTheory.measure_union_le _ _).trans (add_le_add_right ih _)


-- =======================================  MAIN THEOREM  ======================================= --

theorem Polygon.volume_le_pieceAreas (P : Polygon) : Polygon.volume P ≤ Polygon.pieceAreas P :=
  Polygon.aux_union_le P.sets

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

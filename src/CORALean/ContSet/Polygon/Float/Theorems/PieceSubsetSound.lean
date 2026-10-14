module

public import CORALean.ContSet.Polygon.Float.Operations.PieceSubset
public import CORALean.ContSet.Polygon.Float.Theorems.PieceHoldsSound
public import CORALean.ContSet.VPolytope.Real.Theorems.ConvexHull

@[expose] public section

/-!
# A `true` from `Polygon.pieceSubset` proves the inclusion

The first nominal piece is the hull of its vertices, all of them in the second, convex,
nominal piece; and the first box is in the second. A sum of subsets is a subset of the sum.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Polygon.pieceSubset_sound {p q : VPolytope (Vec 𝕋 2)} (h : Polygon.pieceSubset p q = true) :
    p.construct ⊆ q.construct := by -- --- PROOF ---
  simp only [Polygon.pieceSubset, Bool.and_eq_true, List.all_eq_true, List.mem_finRange,
    forall_const] at h
  obtain ⟨hV, hE⟩ := h
  -- the nominal hulls: every vertex of `p` is in the convex nominal `q`
  have hnom : nominalSet p ⊆ nominalSet q := by
    show (nominal p).construct ⊆ (nominal q).construct
    rw [CORALean.Real.VPolytope.construct_eq_convexHull]
    exact convexHull_min (Set.range_subset_iff.mpr fun l => Polygon.pieceHolds_sound (hV l))
      (nominal q).convex_construct
  -- the boxes, corner by corner
  have hbox : p.I_error.construct ⊆ q.I_error.construct := fun e he i =>
    ⟨le_trans (toReal_le_of_le (hE i).1) (he i).1, le_trans (he i).2 (toReal_le_of_le (hE i).2)⟩
  exact Set.add_subset_add hnom hbox

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

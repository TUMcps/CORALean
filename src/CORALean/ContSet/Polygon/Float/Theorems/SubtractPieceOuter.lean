import CORALean.ContSet.Polygon.Float.Operations.SubtractPiece
import CORALean.ContSet.Polygon.Float.Theorems.InnerHRepInner
import CORALean.ContSet.Polygon.Float.Theorems.PieceSubsetSound
import CORALean.ContSet.Interval.Float.Theorems.ContractHalfspaceOuter
import CORALean.ContSet.HPolytope.Float.Theorems.MemConstruct

/-!
# `Polygon.subtractPiece` covers the piece less the other

A point of `r` outside `q` is not covered by `q`, so `pieceSubset` did not drop `r`; outside `q`
it is outside the inner description `H ⊆ q`, so some row `aᵢᵀx ≤ bᵢ` fails, and the point
survives the cut to `-aᵢᵀx ≤ -bᵢ`, which the box hull of `r` and the box-to-polytope
conversion keep. Outer.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Polygon.subtractPiece_outer (q r : VPolytope (Vec 𝕋 2)) :
    r.construct \ q.construct ⊆
      {x | ∃ s ∈ Polygon.subtractPiece q r, x ∈ s.construct} := by -- --- PROOF ---
  rintro x ⟨hr, hq⟩
  -- a piece `q` certainly covers is not dropped
  unfold Polygon.subtractPiece
  by_cases hs : Polygon.pieceSubset r q = true
  · exact absurd (Polygon.pieceSubset_sound hs hr) hq
  rw [if_neg hs]
  -- without an inner description the piece is kept
  rcases hH : Polygon.innerHRep q with _ | H
  · exact ⟨r, by simp, hr⟩
  simp only
  by_cases hme : H.me = 0
  · rw [if_pos hme]
    -- outside `q`, some row of the inner description fails
    have hxH : x ∉ H.construct := fun h => hq (Polygon.innerHRep_inner hH h)
    rw [HPolytope.mem_construct_iff] at hxH
    have hex : ∃ i, toReal (H.b i) < (toRealMat H.A *ᵥ x) i := by
      by_contra hno
      push Not at hno
      exact hxH ⟨hno, fun i => absurd i.2 (by omega)⟩
    obtain ⟨i, hi⟩ := hex
    -- and `x` is in the cut of its row
    refine ⟨_, List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩, ?_⟩
    refine Interval.vPolytope_contains _ (Interval.contractHalfspace_outer _ _ _
      (r.interval_contains hr) ?_)
    simp only [toReal_neg]
    simp only [Matrix.mulVec, dotProduct] at hi
    simp only [neg_mul, Finset.sum_neg_distrib]
    exact neg_le_neg hi.le
  · rw [if_neg hme]
    exact ⟨r, by simp, hr⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

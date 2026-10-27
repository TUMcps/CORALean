module

public import CORALean.ContSet.Polygon.Float.Operations.Subtract
public import CORALean.ContSet.Polygon.Float.Theorems.InnerHRepInner
public import CORALean.ContSet.Polygon.Float.Theorems.PieceSubsetSound
public import CORALean.ContSet.Interval.Float.Theorems.ContractHalfspaceOuter
public import CORALean.ContSet.HPolytope.Float.Theorems.MemConstruct
public import CORALean.ContSet.Conversion.Float.Theorems.IntervalVPolytopeContains
public import CORALean.ContSet.Conversion.Float.Theorems.Basic
public import CORALean.ContSet.Conversion.Real.Theorems.HPolytopeIntervalContains
public import CORALean.ContSet.Conversion.Real.Theorems.HPolytopeVPolytopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.IntervalVPolytopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.VPolytopeIntervalContains
public import CORALean.ContSet.HPolytope.Float.Theorems.Basic
public import CORALean.ContSet.SetUnion.Theorems.Basic

@[expose] public section

/-!
# `Polygon.subtract` encloses the set difference

A point of `P \ Q` lies in a piece `p` of `P`, and stays in the pieces after each piece `q` of
`Q` it is not in (`Polygon.aux_subtractPiece_outer`). Outer for the set difference. The cut pieces
are box hulls, so the result is not claimed to lie in `P`.

## Inputs
* `P` – polygon
* `Q` – polygon

## Hypotheses
* none

## Conclusion
* `Polygon.subtract` encloses the set difference
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

section
open Matrix

/-- `innerHRep` returns the plain inequalities its edges give, with no error box. -/
private theorem Polygon.innerHRep_isErrFree {p : VPolytope (Vec 𝕋 2)} : -- --- CONCL ---
    ∀ H ∈ Polygon.innerHRep p,
      H.IsErrFree := by -- --- PROOF ---
  intro H (h : Polygon.innerHRep p = some H)
  simp only [Polygon.innerHRep] at h
  split_ifs at h
  cases h
  exact HPolytope.isErrFree_of_origin rfl rfl rfl


/-- Subtracting the piece `q` from `r` leaves pieces that cover every point of `r` outside `q`. -/
private theorem Polygon.aux_subtractPiece_outer (q r : VPolytope (Vec 𝕋 2)) : -- --- CONCL ---
    r.construct \ q.construct ⊆
      {x | ∃ s ∈ Polygon.step_subtractPiece q r, x ∈ s.construct} := by -- --- PROOF ---
  rintro x ⟨hr, hq⟩
  -- a piece `q` certainly covers is not dropped
  unfold Polygon.step_subtractPiece
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
    have hxH : x ∉ H.construct := fun h => hq (Polygon.innerHRep_inner _ hH h)
    rw [HPolytope.mem_construct_iff (Polygon.innerHRep_isErrFree _ hH)] at hxH
    have hex : ∃ i, toReal (H.b i) < (toRealMat H.A *ᵥ x) i := by
      by_contra hno
      push Not at hno
      exact hxH ⟨hno, fun i => absurd i.2 (by omega)⟩
    obtain ⟨i, hi⟩ := hex
    -- and `x` is in the cut of its row
    refine ⟨_, List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩, ?_⟩
    refine Interval.vPolytope_contains _ (Interval.contractHalfspace_outer _ _ _
      (r.interval_contains hr) ?_)
    simp only [Pi.neg_apply, toReal_neg, toReal_neg']
    simp only [Matrix.mulVec, dotProduct] at hi
    simp only [neg_mul, Finset.sum_neg_distrib]
    exact neg_le_neg hi.le
  · rw [if_neg hme]
    exact ⟨r, by simp, hr⟩

end


/-- A point in a piece of the list and outside every `q` stays in the folded list. -/
private theorem aux_mem_foldl_subtractPiece {x : Vec ℝ 2}
    (qs L : List (VPolytope (Vec 𝕋 2))) : -- --- CONCL ---
    (∃ r ∈ L, x ∈ r.construct) → (∀ q ∈ qs, x ∉ q.construct) →
      ∃ s ∈ qs.foldl (fun L q => L.flatMap (Polygon.step_subtractPiece q)) L,
      x ∈ s.construct := by -- --- PROOF ---
  induction qs generalizing L with
  | nil => exact fun h _ => h
  | cons q qs ih =>
    rintro ⟨r, hr, hxr⟩ hq
    rw [List.foldl_cons]
    -- the step keeps `x` in some piece, since it is outside `q`
    obtain ⟨s, hs, hxs⟩ := Polygon.aux_subtractPiece_outer q r ⟨hxr, hq q List.mem_cons_self⟩
    exact ih _ ⟨s, List.mem_flatMap.mpr ⟨r, hr, hs⟩, hxs⟩
      (fun q' hq' => hq q' (List.mem_cons_of_mem _ hq'))


-- =======================================  MAIN THEOREM  ======================================= --

theorem Polygon.subtract_outer (P Q : Polygon 𝕋) : -- --- CONCL ---
    ContSet.construct P \ ContSet.construct Q ⊆
    ContSet.construct (Polygon.subtract P Q) := by -- --- PROOF ---
  rintro x ⟨hP, hQ⟩
  obtain ⟨p, hp, hxp⟩ := SetUnion.mem_construct.mp hP
  obtain ⟨s, hs, hxs⟩ := aux_mem_foldl_subtractPiece Q.sets [p] ⟨p, by simp, hxp⟩
    fun q hq hxq => hQ (SetUnion.mem_construct.mpr ⟨q, hq, hxq⟩)
  exact SetUnion.mem_construct.mpr ⟨s, List.mem_flatMap.mpr ⟨p, hp, hs⟩, hxs⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

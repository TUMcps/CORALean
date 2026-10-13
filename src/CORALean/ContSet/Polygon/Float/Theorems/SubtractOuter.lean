module

public import CORALean.ContSet.Polygon.Float.Operations.Subtract
public import CORALean.ContSet.Polygon.Float.Theorems.SubtractPieceOuter

@[expose] public section

/-!
# `Polygon.subtract` encloses the set difference

A point of `P \ Q` lies in a piece `p` of `P`, and stays in the pieces after each piece `q` of
`Q` it is not in (`Polygon.subtractPiece_outer`). Outer for the set difference. The cut pieces
are box hulls, so the result is not claimed to lie in `P`.
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

/-- A point in a piece of the list and outside every `q` stays in the folded list. -/
theorem aux_mem_foldl_subtractPiece {x : Vec ℝ 2} (qs L : List (VPolytope (Vec 𝕋 2))) :
    (∃ r ∈ L, x ∈ r.construct) → (∀ q ∈ qs, x ∉ q.construct) →
      ∃ s ∈ qs.foldl (fun L q => L.flatMap (Polygon.subtractPiece q)) L,
      x ∈ s.construct := by -- --- PROOF ---
  induction qs generalizing L with
  | nil => exact fun h _ => h
  | cons q qs ih =>
    rintro ⟨r, hr, hxr⟩ hq
    rw [List.foldl_cons]
    -- the step keeps `x` in some piece, since it is outside `q`
    obtain ⟨s, hs, hxs⟩ := Polygon.subtractPiece_outer q r ⟨hxr, hq q List.mem_cons_self⟩
    exact ih _ ⟨s, List.mem_flatMap.mpr ⟨r, hr, hs⟩, hxs⟩
      (fun q' hq' => hq q' (List.mem_cons_of_mem _ hq'))


-- =======================================  MAIN THEOREM  ======================================= --

theorem Polygon.subtract_outer (P Q : Polygon 𝕋) :
    ContSet.construct P \ ContSet.construct Q ⊆
    ContSet.construct (Polygon.subtract P Q) := by -- --- PROOF ---
  rintro x ⟨hP, hQ⟩
  obtain ⟨p, hp, hxp⟩ := SetUnion.mem_construct.mp hP
  obtain ⟨s, hs, hxs⟩ := aux_mem_foldl_subtractPiece Q.sets [p] ⟨p, by simp, hxp⟩
    fun q hq hxq => hQ (SetUnion.mem_construct.mpr ⟨q, hq, hxq⟩)
  exact SetUnion.mem_construct.mpr ⟨s, List.mem_flatMap.mpr ⟨p, hp, hs⟩, hxs⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

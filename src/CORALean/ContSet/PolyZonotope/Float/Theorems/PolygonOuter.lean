import CORALean.ContSet.PolyZonotope.Float.Operations.Polygon
import CORALean.ContSet.PolyZonotope.Float.Theorems.SplitLongestGenOuter
import CORALean.ContSet.Zonotope.Float.Theorems.PolygonContains
import CORALean.ContSet.Polygon.Float.Theorems.ConstructOfPieces

/-!
# The float `polygon` encloses the polynomial zonotope

The pieces cover the set after every round (`splitLongestGen_outer`) for every choice of the
pieces to refine, and each piece lies in its zonotope and that in its float `Zonotope.polygon`.
Outer, and no exactness is claimed.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A round keeps the cover. -/
theorem PolyZonotope.aux_polygonRound_cover (pick : PolyZonotope (Vec 𝕋 2) → Bool)
    (L : List (PolyZonotope (Vec 𝕋 2))) {x : Vec ℝ 2} (hx : ∃ q ∈ L, x ∈ q.construct) :
    ∃ q ∈ PolyZonotope.polygonRound pick L, x ∈ q.construct := by -- --- PROOF ---
  obtain ⟨q, hq, hxq⟩ := hx
  unfold PolyZonotope.polygonRound
  by_cases hp : pick q
  · rcases PolyZonotope.splitLongestGen_outer q hxq with h | h
    · exact ⟨q.splitLongestGen.1, List.mem_flatMap.mpr ⟨q, hq, by simp [hp]⟩, h⟩
    · exact ⟨q.splitLongestGen.2, List.mem_flatMap.mpr ⟨q, hq, by simp [hp]⟩, h⟩
  · exact ⟨q, List.mem_flatMap.mpr ⟨q, hq, by simp [hp]⟩, hxq⟩

/-- Every round, so the pieces cover. -/
theorem PolyZonotope.aux_polygonPieces_cover (pZ : PolyZonotope (Vec 𝕋 2))
    (pick : ℕ → PolyZonotope (Vec 𝕋 2) → Bool) (k : ℕ) {x : Vec ℝ 2} (hx : x ∈ pZ.construct) :
    ∃ q ∈ pZ.polygonPieces k pick, x ∈ q.construct := by -- --- PROOF ---
  induction k with
  | zero => exact ⟨pZ, List.mem_singleton_self _, hx⟩
  | succ k ih =>
    unfold PolyZonotope.polygonPieces at ih ⊢
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact PolyZonotope.aux_polygonRound_cover _ _ ih


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.polygon_outer (pZ : PolyZonotope (Vec 𝕋 2)) (splits : ℕ)
    (pick : ℕ → PolyZonotope (Vec 𝕋 2) → Bool) :
    pZ.construct ⊆ ContSet.construct (pZ.polygon splits pick) := by -- --- PROOF ---
  intro x hx
  obtain ⟨q, hq, hxq⟩ := PolyZonotope.aux_polygonPieces_cover pZ pick splits hx
  rw [PolyZonotope.polygon, Polygon.construct_ofPieces]
  refine Set.mem_biUnion (List.mem_map.mpr ⟨q, hq, rfl⟩) ?_
  exact Zonotope.polygon_contains _ (PolyZonotope.zonotope_contains q hxq)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.ContSet.PolyZonotope.Real.Operations.Polygon
public import CORALean.ContSet.PolyZonotope.Real.Theorems.SplitLongestGenUnion
public import CORALean.ContSet.Conversion.Real.Theorems.PolyZonotopeZonotopeEvenContains
public import CORALean.ContSet.Polygon.Real.Theorems.Basic
public import CORALean.ContSet.Conversion.Real.Operations.HPolytope_to_VPolytope
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_VPolytope
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_VPolytope
public import CORALean.ContSet.Conversion.Real.Theorems.Basic
public import CORALean.ContSet.Conversion.Real.Theorems.IntervalVPolytopeExact
public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopeVPolytopeExact

@[expose] public section

/-!
# The polygon of a polynomial zonotope contains it

Whichever pieces are refined, the pieces cover the set (`splitLongestGen_union`) and each lies
in its enclosing zonotope, which is its polygon. An outer statement only: the polygon is the
union of enclosures, larger than the set wherever the enclosures are, and nothing here says how
much.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A round keeps the cover. -/
theorem PolyZonotope.aux_polygonRound_cover (pick : PolyZonotope (Vec ℝ 2) → Bool)
    (L : List (PolyZonotope (Vec ℝ 2))) {x : Vec ℝ 2}
    (hx : ∃ q ∈ L, x ∈ q.construct) :
    ∃ q ∈ PolyZonotope.polygonRound pick L, x ∈ q.construct := by -- --- PROOF ---
  obtain ⟨q, hq, hxq⟩ := hx
  unfold PolyZonotope.polygonRound
  by_cases hp : pick q
  · rw [← PolyZonotope.splitLongestGen_union] at hxq
    rcases hxq with h | h
    · exact ⟨q.splitLongestGen.fst, List.mem_flatMap.mpr ⟨q, hq, by simp [hp]⟩, h⟩
    · exact ⟨q.splitLongestGen.snd, List.mem_flatMap.mpr ⟨q, hq, by simp [hp]⟩, h⟩
  · exact ⟨q, List.mem_flatMap.mpr ⟨q, hq, by simp [hp]⟩, hxq⟩

theorem PolyZonotope.aux_polygonPieces_cover (pZ : PolyZonotope (Vec ℝ 2))
    (pick : ℕ → PolyZonotope (Vec ℝ 2) → Bool) (k : ℕ) {x : Vec ℝ 2} (hx : x ∈ pZ.construct) :
    ∃ q ∈ pZ.polygonPieces k pick, x ∈ q.construct := by -- --- PROOF ---
  induction k with
  | zero => exact ⟨pZ, List.mem_singleton_self _, hx⟩
  | succ k ih =>
    unfold PolyZonotope.polygonPieces at ih ⊢
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact PolyZonotope.aux_polygonRound_cover _ _ ih


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.polygon_outer (pZ : PolyZonotope (Vec ℝ 2)) (splits : ℕ)
    (pick : ℕ → PolyZonotope (Vec ℝ 2) → Bool) :
    pZ.construct ⊆ ContSet.construct (pZ.polygon splits pick) := by -- --- PROOF ---
  intro x hx
  obtain ⟨q, hq, hxq⟩ := PolyZonotope.aux_polygonPieces_cover pZ pick splits hx
  rw [PolyZonotope.polygon, Polygon.construct_ofPieces]
  refine Set.mem_biUnion (List.mem_map.mpr ⟨q, hq, rfl⟩) ?_
  show x ∈ q.zonotopeEven.vPolytope.construct
  rw [Zonotope.vPolytope_exact]
  exact PolyZonotope.zonotopeEven_contains q hxq

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

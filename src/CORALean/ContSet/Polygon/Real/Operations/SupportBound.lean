import CORALean.ContSet.Polygon.Real.Theorems.VerticesHull

/-!
# `Polygon.supportBound`

CORA's `@polygon/supportFunc_` at `upper`: the largest value of the direction over the vertices.
An upper bound on the support function, which it equals for a nonempty polygon: the polygon lies
in the hull of its vertices (`Polygon.convexHull_vertices`) and the half-space under the largest
vertex value is convex. A polygon without a vertex is empty, and then `0` is as good a bound as
any (CORA gives `-Inf`, outside ℝ).
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

theorem Polygon.aux_le_foldr_max (l : List ℝ) (s : ℝ) {a : ℝ} (h : a ∈ l) :
    a ≤ l.foldr max s := by -- --- PROOF ---
  induction l with
  | nil => exact absurd h (List.not_mem_nil)
  | cons b l ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact le_max_left _ _
    · exact le_trans (ih h) (le_max_right _ _)


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The largest value of `c` over the vertices, seeded with the first one; `0` if there are none. -/
noncomputable def Polygon.supportBound (P : Polygon) (c : Vec ℝ 2 →ₗ[ℝ] ℝ) :
    SupportBound (ContSet.construct P) c where
  val := (P.vertices.map c).foldr max ((P.vertices.map c).headD 0)
  le x hx := by
    -- the polygon lies in the hull of its vertices, and the half-space under the bound is convex
    have hhull : convexHull ℝ {v | v ∈ P.vertices} ⊆
        {y | c y ≤ (P.vertices.map c).foldr max ((P.vertices.map c).headD 0)} :=
      convexHull_min (fun v hv => Polygon.aux_le_foldr_max _ _ (List.mem_map_of_mem hv))
        (convex_halfSpace_le c.isLinear _)
    exact hhull (Polygon.convexHull_vertices P ▸ subset_convexHull ℝ _ hx)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

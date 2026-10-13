module

public import CORALean.ContSet.Polygon.Real.Operations.Triangulation
public import CORALean.ContSet.Conversion.Real.VPolytope_to_PolyZonotope
public import CORALean.ContSet.PolyZonotope.Real.Operations.QuadMapMixed
public import CORALean.ContSet.PolyZonotope.Real.Operations.Polygon

@[expose] public section

/-!
# `Polygon.quadMapMixed`

CORA's `polygon/quadMap(pgon₁, pgon₂, Q)`: the map `(x₁, x₂) ↦ (x₁ᵀ Q₁ x₂, x₁ᵀ Q₂ x₂)` of a
point of each polygon, over every pair of triangles of the two triangulations. CORA's loop over
`j` builds the second polytope from `list2{i}` where `list2{j}` is meant (FINDINGS.md); here the
pair is `(list1{i}, list2{j})`. Otherwise as `Polygon.quadMap`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The union of the polygons of the images of the pairs of triangles. -/
noncomputable def Polygon.quadMapMixed (P₁ P₂ : Polygon) (Q : Fin 2 → Mat ℝ 2 2) (splits : ℕ)
    (pick : ℕ → PolyZonotope (Vec ℝ 2) → Bool) : Polygon :=
  -- `list1 = triangulation(pgon1)` and `list2 = triangulation(pgon2)`
  let list₁ : List (VPolytope (Vec ℝ 2)) := (Polygon.triangulation P₁).sets
  let list₂ : List (VPolytope (Vec ℝ 2)) := (Polygon.triangulation P₂).sets
  -- per pair `pZ_i_2 = quadMap(pZ1, polyZonotope(polytope(list2{j})), Q)`, then `polygon(pZ_i_2)`
  ⟨list₁.flatMap fun t₁ => list₂.flatMap fun t₂ =>
    ((PolyZonotope.quadMapMixed Q t₁.polyZonotope t₂.polyZonotope).polygon splits pick).sets⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

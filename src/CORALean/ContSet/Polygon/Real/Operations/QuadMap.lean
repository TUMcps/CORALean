module

public import CORALean.ContSet.Polygon.Real.Operations.Triangulation
public import CORALean.ContSet.Conversion.Real.VPolytope_to_PolyZonotope
public import CORALean.ContSet.PolyZonotope.Real.Operations.QuadMap
public import CORALean.ContSet.PolyZonotope.Real.Operations.Polygon

@[expose] public section

/-!
# `Polygon.quadMap`

CORA's `polygon/quadMap(pgon, Q)` for the quadratic map `x ↦ (xᵀ Q₁ x, xᵀ Q₂ x)` of the plane:
triangulate the polygon, map each triangle as a polynomial zonotope (`polyZonotope(polytope(·))`
then `quadMap`), take the `polygon` of each image and unite them. The triangles are those of
`Polygon.triangulation`, a cover (the union over a cover is the union over a partition). The
`polygon` of a polynomial zonotope is `PolyZonotope.polygon` with its `splits` and `pick`
parameters, and the conversion to a polynomial zonotope goes through the triangle's box
(`VPolytope.polyZonotope`), so the result is an enclosure, not CORA's tight sampled boundary.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The union of the polygons of the images of the triangles. -/
noncomputable def Polygon.quadMap (P : Polygon) (Q : Fin 2 → Mat ℝ 2 2) (splits : ℕ)
    (pick : ℕ → PolyZonotope (Vec ℝ 2) → Bool) : Polygon :=
  -- `list = triangulation(pgon)`
  let list : List (VPolytope (Vec ℝ 2)) := (Polygon.triangulation P).sets
  -- per triangle `pZ_i_2 = quadMap(polyZonotope(polytope(list{i})), Q)`, then `polygon(pZ_i_2)`
  ⟨list.flatMap fun t => ((t.polyZonotope.quadMap Q).polygon splits pick).sets⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

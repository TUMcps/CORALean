module

public import CORALean.ContSet.Polygon.Real.Operations.QuadMapMixed
public import CORALean.ContSet.Polygon.Real.Theorems.TriangulationExact
public import CORALean.ContSet.PolyZonotope.Real.Theorems.QuadMapMixedExact
public import CORALean.ContSet.PolyZonotope.Real.Theorems.PolygonOuter
public import CORALean.ContSet.Conversion.Real.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_PolyZonotope
public import CORALean.ContSet.Conversion.Real.Theorems.Basic

@[expose] public section

/-!
# `Polygon.quadMapMixed` encloses the image of the product of the regions

Outer, as `Polygon.quadMap_outer`, with the pair of triangles that holds the pair of points.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem Polygon.quadMapMixed_outer (P₁ P₂ : Polygon) (Q : Fin 2 → Mat ℝ 2 2) (splits : ℕ)
    (pick : ℕ → PolyZonotope (Vec ℝ 2) → Bool) : -- --- STMT ---
    (fun x : Vec ℝ 2 × Vec ℝ 2 => PolyZonotope.quadBilin Q x.1 x.2)
        '' (ContSet.construct P₁ ×ˢ ContSet.construct P₂)
      ⊆ ContSet.construct (P₁.quadMapMixed P₂ Q splits pick) := by -- --- PROOF ---
  rintro _ ⟨⟨x₁, x₂⟩, ⟨hx₁, hx₂⟩, rfl⟩
  rw [← (Polygon.triangulation_exact P₁).2] at hx₁
  rw [← (Polygon.triangulation_exact P₂).2] at hx₂
  obtain ⟨t₁, ht₁, hxt₁⟩ := SetUnion.mem_construct.mp hx₁
  obtain ⟨t₂, ht₂, hxt₂⟩ := SetUnion.mem_construct.mp hx₂
  -- the pair of points is mapped into the image of the pair of polynomial zonotopes
  have himg : PolyZonotope.quadBilin Q x₁ x₂ ∈
      (PolyZonotope.quadMapMixed Q t₁.polyZonotope t₂.polyZonotope).construct :=
    (PolyZonotope.quadMapMixed_exact Q t₁.polyZonotope t₂.polyZonotope).subset
      ⟨(x₁, x₂), ⟨VPolytope.polyZonotope_contains t₁ hxt₁,
        VPolytope.polyZonotope_contains t₂ hxt₂⟩, rfl⟩
  have hpoly := PolyZonotope.polygon_outer
    (PolyZonotope.quadMapMixed Q t₁.polyZonotope t₂.polyZonotope) splits pick himg
  obtain ⟨s, hs, hxs⟩ := SetUnion.mem_construct.mp hpoly
  exact SetUnion.mem_construct.mpr
    ⟨s, List.mem_flatMap.mpr ⟨t₁, ht₁, List.mem_flatMap.mpr ⟨t₂, ht₂, hs⟩⟩, hxs⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

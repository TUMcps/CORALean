import CORALean.ContSet.Polygon.Float.Operations.QuadMapMixed
import CORALean.ContSet.Polygon.Float.Theorems.TriangulationExact
import CORALean.ContSet.PolyZonotope.Float.Theorems.QuadMapMixedOuter
import CORALean.ContSet.PolyZonotope.Float.Theorems.PolygonOuter

/-!
# `Polygon.quadMapMixed` encloses the image of the product of the float polygons

Outer, as `Polygon.quadMap_outer`, with the pair of triangles that holds the pair of points.
-/

-- Authors:       Tobias Ladner
-- Written:       10-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Polygon.quadMapMixed_outer (P₁ P₂ : Polygon 𝕋) (Q : Fin 2 → Mat 𝕋 2 2) (splits : ℕ)
    (pick : ℕ → PolyZonotope (Vec 𝕋 2) → Bool) :
    (fun x : Vec ℝ 2 × Vec ℝ 2 => Real.PolyZonotope.quadBilin (fun k => toRealMat (Q k)) x.1 x.2)
        '' (ContSet.construct P₁ ×ˢ ContSet.construct P₂)
      ⊆ ContSet.construct (P₁.quadMapMixed P₂ Q splits pick) := by -- --- PROOF ---
  rintro _ ⟨⟨x₁, x₂⟩, ⟨hx₁, hx₂⟩, rfl⟩
  rw [← (Polygon.triangulation_exact P₁).2] at hx₁
  rw [← (Polygon.triangulation_exact P₂).2] at hx₂
  obtain ⟨t₁, ht₁, hxt₁⟩ := SetUnion.mem_construct.mp hx₁
  obtain ⟨t₂, ht₂, hxt₂⟩ := SetUnion.mem_construct.mp hx₂
  -- the pair of points is mapped into the image of the pair of polynomial zonotopes
  have himg := PolyZonotope.quadMapMixed_outer Q t₁.polyZonotope t₂.polyZonotope
    ⟨(x₁, x₂), ⟨VPolytope.polyZonotope_contains t₁ hxt₁,
      VPolytope.polyZonotope_contains t₂ hxt₂⟩, rfl⟩
  have hpoly := PolyZonotope.polygon_outer
    (PolyZonotope.quadMapMixed Q t₁.polyZonotope t₂.polyZonotope) splits pick himg
  obtain ⟨s, hs, hxs⟩ := SetUnion.mem_construct.mp hpoly
  exact SetUnion.mem_construct.mpr
    ⟨s, List.mem_flatMap.mpr ⟨t₁, ht₁, List.mem_flatMap.mpr ⟨t₂, ht₂, hs⟩⟩, hxs⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.ContSet.ZonoBundle.Real.Operations.ConvHull
public import CORALean.ContSet.Conversion.Real.VPolytope_to_ConZonotope
public import CORALean.ContSet.ConZonotope.Real.Theorems.ExistsConstructEqIffHPolytope

@[expose] public section

/-!
# The convex hull of two bundles has a halfspace description

The hull of the two bundles is the hull of the joined vertices, a vertex polytope, hence a
constrained zonotope (`VPolytope.conZonotope_exact`), hence a bounded halfspace description.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.exists_hPolytope_convHull (zB₁ zB₂ : ZonoBundle (Vec ℝ n))
    (hk₁ : 0 < zB₁.k) (hk₂ : 0 < zB₂.k) (hne₁ : zB₁.construct.Nonempty)
    (hne₂ : zB₂.construct.Nonempty) :
    ∃ P : HPolytope (Vec ℝ n),
      P.construct = convexHull ℝ (zB₁.construct ∪ zB₂.construct) := by -- --- PROOF ---
  have hV := VPolytope.convHull_exact (zB₁.vPolytopeAll hk₁ hne₁) (zB₂.vPolytopeAll hk₂ hne₂)
  rw [ZonoBundle.vPolytopeAll_exact, ZonoBundle.vPolytopeAll_exact] at hV
  -- the joined vertices denote the hull, so their constrained zonotope does
  have hc : (zB₁.encloseTightVertices zB₂ hk₁ hk₂ hne₁ hne₂).conZonotope.construct
      = convexHull ℝ (zB₁.construct ∪ zB₂.construct) := by
    rw [← VPolytope.conZonotope_exact]
    exact hV
  obtain ⟨P, hP, -⟩ := ConZonotope.exists_construct_eq_iff_hPolytope.mp ⟨_, hc⟩
  exact ⟨P, hP⟩


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

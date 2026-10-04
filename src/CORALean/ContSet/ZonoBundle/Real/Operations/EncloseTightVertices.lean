import CORALean.ContSet.Conversion.Real.ZonoBundle_to_VPolytope
import CORALean.ContSet.VPolytope.Real.Operations.ConvHull
import CORALean.ContSet.VPolytope.Real.Theorems.ConvHullExact

/-!
# `ZonoBundle.encloseTightVertices`

`V = vertices([V1, V2])` of CORA's `encloseTight`: the vertices of the two bundles joined, which are
those of the exact `conZonotope(zB)` (`vPolytopeAll`), as `vertices` does without discarding the
interior ones. Both bundles must be nonempty and have a member.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The vertices of the two bundles joined. -/
noncomputable def ZonoBundle.encloseTightVertices (zB₁ zB₂ : ZonoBundle (Vec ℝ n))
    (hk₁ : 0 < zB₁.k) (hk₂ : 0 < zB₂.k) (hne₁ : zB₁.construct.Nonempty)
    (hne₂ : zB₂.construct.Nonempty) : VPolytope (Vec ℝ n) :=
  (zB₁.vPolytopeAll hk₁ hne₁).convHull (zB₂.vPolytopeAll hk₂ hne₂)


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

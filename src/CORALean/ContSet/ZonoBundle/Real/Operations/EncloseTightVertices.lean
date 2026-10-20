module

public import CORALean.ContSet.Conversion.Real.Operations.ZonoBundle_to_VPolytope
public import CORALean.ContSet.VPolytope.Real.Operations.ConvHull
public import CORALean.ContSet.VPolytope.Real.Theorems.ConvHullExact

@[expose] public section

/-!
# `ZonoBundle.encloseTightVertices`

`V = vertices([V1, V2])` of CORA's `encloseTight`: the vertices of the two bundles joined, which are
those of the exact `conZonotope(zB)` (`vPolytopeAll`), as `vertices` does without discarding the
interior ones. Both bundles must be nonempty and have a member.

## Inputs
* `zB₁` – first bundle
* `zB₂` – second bundle

## Hypotheses
* `hk₁` – first bundle has a member
* `hk₂` – second bundle has a member
* `hne₁` – first bundle nonempty
* `hne₂` – second bundle nonempty

## Output
* the vertices of the two bundles joined
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


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

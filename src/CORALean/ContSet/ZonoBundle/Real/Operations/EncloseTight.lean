import CORALean.ContSet.ZonoBundle.Real.Operations.EncloseTightPoints
import CORALean.ContSet.ZonoBundle.Real.Operations.EncloseTightVerticesNonempty
import CORALean.ContSet.VPolytope.Real.Operations.KNeZeroOfNonempty

/-!
# `ZonoBundle.encloseTight`

CORA's `@zonoBundle/encloseTight(zB1, zB2, W)`: `encloseTightPoints` of the vertices of the two
bundles (`V = vertices([V1, V2])`, `encloseTightVertices`). Both bundles must be nonempty and have
a member; `W` the transformations and `U` the Stursberg basis, as in `encloseTightPoints`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n r : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `encloseTight(zB1, zB2, W)`. -/
noncomputable def ZonoBundle.encloseTight (zB₁ zB₂ : ZonoBundle (Vec ℝ n))
    (hk₁ : 0 < zB₁.k) (hk₂ : 0 < zB₂.k) (hne₁ : zB₁.construct.Nonempty)
    (hne₂ : zB₂.construct.Nonempty) (W : Fin r → Mat ℝ n n) (U : Mat ℝ n n) :
    ZonoBundle (Vec ℝ n) :=
  let V := zB₁.encloseTightVertices zB₂ hk₁ hk₂ hne₁ hne₂            -- vertices([V1, V2])
  haveI : NeZero V.k := ⟨VPolytope.k_ne_zero_of_nonempty
    (ZonoBundle.encloseTightVertices_nonempty zB₁ zB₂ hk₁ hk₂ hne₁ hne₂)⟩
  ZonoBundle.encloseTightPoints V.V W U


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

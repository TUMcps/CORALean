module

public import CORALean.ContSet.ZonoBundle.Real.Operations.EncloseTight
public import CORALean.ContSet.ZonoBundle.Real.Theorems.EncloseTightPointsMem
public import CORALean.ContSet.ZonoBundle.Real.Theorems.Basic
public import CORALean.ContSet.Conversion.Real.Operations.ZonoBundle_to_VPolytope
public import CORALean.ContSet.Conversion.Real.Theorems.Basic

@[expose] public section

/-!
# The tight enclosure of two bundles contains both

Every point of `V` lies in the bundle (`encloseTightPoints_mem`), and the bundle being convex, so
does their hull. With `V` the vertices of the two bundles (`vPolytopeAll_exact`, whose hull is the
bundle), both are inside: an outer enclosure of the union, and of its convex hull. An enclosure,
not an exact statement: the result is a bundle of boxes in the chosen coordinates, larger than the
convex hull in general.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n r : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.encloseTight_outer (zB₁ zB₂ : ZonoBundle (Vec ℝ n))
    (hk₁ : 0 < zB₁.k) (hk₂ : 0 < zB₂.k) (hne₁ : zB₁.construct.Nonempty)
    (hne₂ : zB₂.construct.Nonempty) (W : Fin r → Mat ℝ n n) (hW : ∀ i, IsUnit (W i).det)
    {U : Mat ℝ n n} (hU : U * Uᵀ = 1) : -- --- STMT ---
    convexHull ℝ (zB₁.construct ∪ zB₂.construct)
      ⊆ (zB₁.encloseTight zB₂ hk₁ hk₂ hne₁ hne₂ W U).construct := by -- --- PROOF ---
  -- the joined vertices span both bundles
  have hV := VPolytope.convHull_exact (zB₁.vPolytopeAll hk₁ hne₁) (zB₂.vPolytopeAll hk₂ hne₂)
  rw [ZonoBundle.vPolytopeAll_exact, ZonoBundle.vPolytopeAll_exact] at hV
  have hV' : (zB₁.encloseTightVertices zB₂ hk₁ hk₂ hne₁ hne₂).construct
      = convexHull ℝ (zB₁.construct ∪ zB₂.construct) := hV
  rw [← hV', VPolytope.construct_eq_convexHull]
  -- the bundle is convex and holds every vertex
  refine convexHull_min ?_ (SetIntersection.convex_construct _)
  rintro _ ⟨j, rfl⟩
  haveI : NeZero (zB₁.encloseTightVertices zB₂ hk₁ hk₂ hne₁ hne₂).k :=
    ⟨VPolytope.k_ne_zero_of_nonempty
      (ZonoBundle.encloseTightVertices_nonempty zB₁ zB₂ hk₁ hk₂ hne₁ hne₂)⟩
  exact ZonoBundle.encloseTightPoints_mem _ W hW hU j


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

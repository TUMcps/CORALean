import CORALean.ContSet.ZonoBundle.Real.Operations.ConvHull

/-!
# `convHull_` of two bundles is exact

`zonoBundle(P)` of a polytope loses nothing (`HPolytope.zonoBundleRows_exact`), so the bundle
`convHull_` returns denotes exactly the convex hull of the union, given a halfspace description `P`
of the hull (it exists, `exists_hPolytope_convHull`) and Gram-Schmidt bases of its rows.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.convHull_exact [NeZero n] (zB₁ zB₂ : ZonoBundle (Vec ℝ n))
    (hk₁ : 0 < zB₁.k) (hk₂ : 0 < zB₂.k) (hne₁ : zB₁.construct.Nonempty)
    (hne₂ : zB₂.construct.Nonempty) (P : HPolytope (Vec ℝ n))
    (hP : P.construct = convexHull ℝ (zB₁.construct ∪ zB₂.construct))
    (B : Fin (P.m + (P.me + P.me)) → Mat ℝ n n) (hB : ∀ i, B i * (B i)ᵀ = 1)
    (hrow : ∀ i x, P.rows i x = HPolytope.rowNorm (P.rows i) * ((B i)ᵀ *ᵥ x) 0) :
    (zB₁.convHull zB₂ hk₁ hk₂ hne₁ hne₂ P B).construct
      = convexHull ℝ (zB₁.construct ∪ zB₂.construct) := by -- --- PROOF ---
  -- the joined vertices span the hull
  have hV := VPolytope.convHull_exact (zB₁.vPolytopeAll hk₁ hne₁) (zB₂.vPolytopeAll hk₂ hne₂)
  rw [ZonoBundle.vPolytopeAll_exact, ZonoBundle.vPolytopeAll_exact] at hV
  haveI : NeZero (zB₁.encloseTightVertices zB₂ hk₁ hk₂ hne₁ hne₂).k :=
    ⟨VPolytope.k_ne_zero_of_nonempty
      (ZonoBundle.encloseTightVertices_nonempty zB₁ zB₂ hk₁ hk₂ hne₁ hne₂)⟩
  -- and `zonoBundle(P)` of the polytope is the polytope
  rw [← hP]
  exact P.zonoBundleRows_exact _ B (hV.trans hP.symm) hB hrow


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

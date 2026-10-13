import CORALean.ContSet.ZonoBundle.Real.Operations.EncloseTight
import CORALean.ContSet.Conversion.Real.HPolytope_to_ZonoBundle

/-!
# `ZonoBundle.convHull`

CORA's `@zonoBundle/convHull_` for a second operand that is nonempty and convertible to a polytope:
`P = convHull(polytope(zB), polytope(S))` and `S_out = zonoBundle(P)`. The hull of two polytopes is
a polytope whose halfspaces and vertices CORA gets from a convex-hull routine, and `zonoBundle(P)`
is `HPolytope.zonoBundleRows` on them (`polytope/zonoBundle`).

The halfspace description `P` of the hull and the orthogonal bases `B` (Gram-Schmidt of the rows)
are arguments; the vertices are those of the two bundles joined (`encloseTightVertices`), which span
the hull. CORA returns the other operand when one is empty, which is not modelled: both bundles
are nonempty and have a member.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `zonoBundle(convHull(polytope(zB1), polytope(zB2)))`, for `P` the hull's description. -/
noncomputable def ZonoBundle.convHull [NeZero n] (zB₁ zB₂ : ZonoBundle (Vec ℝ n))
    (hk₁ : 0 < zB₁.k) (hk₂ : 0 < zB₂.k) (hne₁ : zB₁.construct.Nonempty)
    (hne₂ : zB₂.construct.Nonempty) (P : HPolytope (Vec ℝ n))
    (B : Fin (P.m + (P.me + P.me)) → Mat ℝ n n) : ZonoBundle (Vec ℝ n) :=
  let V := zB₁.encloseTightVertices zB₂ hk₁ hk₂ hne₁ hne₂           -- vertices of the hull
  haveI : NeZero V.k := ⟨VPolytope.k_ne_zero_of_nonempty
    (ZonoBundle.encloseTightVertices_nonempty zB₁ zB₂ hk₁ hk₂ hne₁ hne₂)⟩
  P.zonoBundleRows V B                                               -- zonoBundle(P)


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

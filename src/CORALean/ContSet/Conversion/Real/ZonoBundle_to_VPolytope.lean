import CORALean.ContSet.Conversion.Real.ZonoBundle_to_Zonotope
import CORALean.ContSet.Conversion.Real.Zonotope_to_VPolytope
import CORALean.ContSet.Conversion.Real.ZonoBundle_to_ConZonotope
import CORALean.ContSet.Conversion.Real.ConZonotope_to_VPolytope

/-!
# A bundle's corners, at one component

Through `ZonoBundle.zonotope i`, then that zonotope's own `2ʰ` sign corners.
Whichever component `i` names already throws away every other one the bundle
intersects against — the whole point of a bundle being that the intersection is
tighter than any one member. The corner step is exact, so all the loss is the
choice of component.

`vPolytopeAll` keeps every member, as CORA's `vertices_` of a bundle does (through
`polytope(zB)`, the intersection of the members' polytopes): the vertices of the exact
`conZonotope(zB)` (`conZonotopeAll`), whose vertex list spans it. It needs a nonempty bundle, where
CORA returns an empty vertex list; and the vertices listed are the corners of the coefficient
polytope's vertices carried through the generators, not only the extreme points of the bundle, so
the list may hold interior points: the hull is the bundle, which `vPolytopeAll_exact` proves.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}

noncomputable def ZonoBundle.vPolytope (zB : ZonoBundle (Vec ℝ n)) (i : Fin zB.k) :
    VPolytope (Vec ℝ n) :=
  (zB.zonotope i).vPolytope


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.vPolytope_contains (zB : ZonoBundle (Vec ℝ n)) (i : Fin zB.k) :
    zB.construct ⊆ (zB.vPolytope i).construct :=
  subset_trans (zB.zonotope_contains i) (Zonotope.vPolytope_contains _)


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The coefficient domain of `conZonotope(zB)` is nonempty when the bundle is. -/
theorem ZonoBundle.aux_domain_nonempty (zB : ZonoBundle (Vec ℝ n)) (hk : 0 < zB.k)
    (hne : zB.construct.Nonempty) :
    (zB.conZonotopeAll hk).domain.construct.Nonempty := by
  obtain ⟨x, hx⟩ := hne
  rw [← ZonoBundle.conZonotopeAll_exact zB hk] at hx
  obtain ⟨β, hb, hP, -⟩ := hx
  exact ⟨β, ConZonotope.mem_domain_iff.mpr ⟨hb, hP⟩⟩


/-- CORA's `vertices_` of a bundle: the vertices of `conZonotope(zB)`. -/
noncomputable def ZonoBundle.vPolytopeAll (zB : ZonoBundle (Vec ℝ n)) (hk : 0 < zB.k)
    (hne : zB.construct.Nonempty) : VPolytope (Vec ℝ n) :=
  (zB.conZonotopeAll hk).vPolytope (zB.aux_domain_nonempty hk hne)

/-- Exact: the vertex list spans the bundle. -/
theorem ZonoBundle.vPolytopeAll_exact (zB : ZonoBundle (Vec ℝ n)) (hk : 0 < zB.k)
    (hne : zB.construct.Nonempty) : (zB.vPolytopeAll hk hne).construct = zB.construct :=
  (ConZonotope.vPolytope_exact _ _).trans (ZonoBundle.conZonotopeAll_exact zB hk)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

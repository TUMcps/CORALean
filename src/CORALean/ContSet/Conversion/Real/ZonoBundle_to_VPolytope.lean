module

public import CORALean.ContSet.Conversion.Real.ZonoBundle_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Zonotope_to_VPolytope
public import CORALean.ContSet.Conversion.Real.ZonoBundle_to_ConZonotope
public import CORALean.ContSet.Conversion.Real.ConZonotope_to_VPolytope
public import CORALean.ContSet.Conversion.Real.Operations.ZonoBundle_to_VPolytope

@[expose] public section

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


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.vPolytope_contains (zB : ZonoBundle (Vec ℝ n)) (i : Fin zB.k) :
    zB.construct ⊆ (zB.vPolytope i).construct :=
  subset_trans (zB.zonotope_contains i) (Zonotope.vPolytope_contains _)

/-- Exact: the vertex list spans the bundle. -/
theorem ZonoBundle.vPolytopeAll_exact (zB : ZonoBundle (Vec ℝ n)) (hk : 0 < zB.k)
    (hne : zB.construct.Nonempty) : (zB.vPolytopeAll hk hne).construct = zB.construct :=
  (ConZonotope.vPolytope_exact _ _).trans (ZonoBundle.conZonotopeAll_exact zB hk)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.ContSet.HPolytope.Real.Theorems.Convex
public import CORALean.ContSet.PolyZonotope.Real.Theorems.IsPolytopeCexNotConvex

@[expose] public section

/-!
# A polynomial zonotope that is no polytope

A polytope is a polynomial zonotope (`VPolytope.exists_polyZonotope_exact`), and the inclusion is
strict: `PolyZonotope.isPolytopeCex` is not convex, and a halfspace description always is.

This is the arrow from polytopes to polynomial zonotopes of
[1, Fig. 1 (Polytopes → Polynomial Zonotopes)].

## References

* [1] N. Kochdumper and M. Althoff. "Sparse Polynomial Zonotopes: A Novel Set
      Representation for Reachability Analysis". IEEE Transactions on Automatic
      Control, 2021.

-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.exists_not_hPolytope :
    ∃ pZ : PolyZonotope (Vec ℝ 2), ¬ ∃ P : HPolytope (Vec ℝ 2), P.construct = pZ.construct :=
  ⟨PolyZonotope.isPolytopeCex, fun ⟨P, h⟩ =>
    PolyZonotope.isPolytopeCex_not_convex (h ▸ P.convex_construct)⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

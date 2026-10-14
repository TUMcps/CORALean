module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import CORALean.ContSet.Zonotope.Real.Theorems.Convex
public import CORALean.ContSet.VPolytope.Real.VPolytope
public import CORALean.ContSet.VPolytope.Real.Theorems.ConvexHull
public import CORALean.Global.Corners
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_VPolytope
public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopeVPolytopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopeContainsVPolytope

@[expose] public section

/-!
# A zonotope as its corners

CORA's `polytope(zonotope)`: `2ʰ` vertices, one per choice of sign per
generator. Exponential in the generator count, which is what makes it the
conversion CORA avoids — but it loses nothing, every point of the zonotope being
a convex combination of the sign corners, and every such combination lying back
in the zonotope since it is convex — `vPolytope_exact` is [1, Eq. 9], read at
any generator's larger (non-minimal) corner set, `Zonotope (Mat ℝ n n)` being
[1, Eq. 8]'s matrix zonotope.

The same weights as a box's corners, and for the same reason: a box *is* the
zonotope with axis-aligned generators. A coefficient `βⱼ ∈ [-1, 1]` sits a
fraction `(βⱼ + 1)/2` of the way from `-1` to `1`, a corner's weight is the
product of those fractions and their complements, and every generator's weight
sums back to its own coefficient while the rest sum away.

## References

* [1] M. Althoff, B. H. Krogh and O. Stursberg. "Analyzing Reachability of Linear
      Dynamic Systems with Parametric Uncertainties". In A. Rauh and E. Auer (eds.),
      Modeling, Design, and Simulation of Systems with Uncertainties, Springer, 2011.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.vPolytope_exact (Z : Zonotope α) :
    Z.vPolytope.construct = Z.construct :=
  Set.Subset.antisymm Z.contains_vPolytope Z.vPolytope_contains

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

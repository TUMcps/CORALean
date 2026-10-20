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

CORA's `polytope(zonotope)`: `2ʰ` vertices, one per choice of sign per generator. Exponential in the
generator count, the conversion CORA avoids, but it loses nothing: every point of the zonotope is a
convex combination of the sign corners, and every such combination lies back in it.
`vPolytope_exact` is [1, Eq. 9], with `Zonotope (Mat ℝ n n)` [1, Eq. 8]'s matrix zonotope. The
weights are a box's corners', a box being the zonotope with axis-aligned generators: a coefficient
`βⱼ ∈ [-1, 1]` sits a fraction `(βⱼ + 1)/2` of the way up, and a corner's weight is the product of
those fractions and their complements. This is the arrow from zonotopes to polytopes of
[2, Fig. 1 (Zonotopes → Polytopes)].

## Inputs
* `Z` – zonotope

## Hypotheses
* none

## Conclusion
* vertex polytope equals the zonotope

## References

* [1] M. Althoff, B. H. Krogh and O. Stursberg. "Analyzing Reachability of Linear
      Dynamic Systems with Parametric Uncertainties". In A. Rauh and E. Auer (eds.),
      Modeling, Design, and Simulation of Systems with Uncertainties, Springer, 2011.
* [2] N. Kochdumper and M. Althoff. "Sparse Polynomial Zonotopes: A Novel Set
      Representation for Reachability Analysis". IEEE Transactions on Automatic
      Control, 2021.
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

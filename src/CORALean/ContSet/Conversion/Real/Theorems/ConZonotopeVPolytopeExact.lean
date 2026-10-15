module

public import CORALean.ContSet.ConZonotope.Real.Operations.Domain
public import CORALean.ContSet.ConZonotope.Real.Operations.MemDomainIff
public import CORALean.ContSet.ConZonotope.Real.Theorems.Convex
public import CORALean.ContSet.ConZonotope.Real.Theorems.IsCompactDomain
public import CORALean.ContSet.Conversion.Real.Theorems.HPolytopeContainsVPolytope
public import CORALean.ContSet.Conversion.Real.Theorems.HPolytopeVPolytopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.IntervalVPolytopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.IntervalContainsVPolytope
public import CORALean.ContSet.Conversion.Real.Operations.ConZonotope_to_VPolytope
public import CORALean.ContSet.Conversion.Real.Theorems.ConZonotopeVPolytopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.ConZonotopeContainsVPolytope
public import CORALean.ContSet.Conversion.Real.Operations.HPolytope_to_VPolytope
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_VPolytope

@[expose] public section

/-!
# A constrained zonotope as its vertices

Exact, and the one conversion out of a constrained zonotope that loses nothing.

The coefficients live in a halfspace description — the unit box intersected with
the constraints — and that description is bounded, the unit box seeing to it. So
its vertices can be enumerated exactly, and the generators carry each of them to
a point of the set. A combination of coefficients maps to the same combination of
those points, the map being affine and the weights summing to one.

Costs whatever the coefficient domain's enumeration costs, which is `2^m` in its
constraint count. Every cheaper route out of a constrained zonotope drops the
constraints first and pays for it in precision instead.

This is the equivalence of polytopes and constrained zonotopes of
[1, Fig. 1 (Polytopes ↔ Constrained Zonotopes)].

## References

* [1] N. Kochdumper and M. Althoff. "Sparse Polynomial Zonotopes: A Novel Set
      Representation for Reachability Analysis". IEEE Transactions on Automatic
      Control, 2021.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.vPolytope_exact (cZ : ConZonotope α) (hne : cZ.domain.construct.Nonempty) :
    (cZ.vPolytope hne).construct = cZ.construct :=
  Set.Subset.antisymm (cZ.contains_vPolytope hne) (cZ.vPolytope_contains hne)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

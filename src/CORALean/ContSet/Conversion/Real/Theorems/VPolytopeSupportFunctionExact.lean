module

public import CORALean.ContSet.Conversion.Real.Operations.VPolytope_to_SupportFunction
public import CORALean.ContSet.SupportFunction.Real.Theorems.OfSetExact
public import CORALean.ContSet.VPolytope.Real.Theorems.Basic
public import CORALean.ContSet.VPolytope.Real.Theorems.Convex

@[expose] public section

/-!
# A polytope by vertices as a support function

Exact: the convex hull of finitely many points is compact, hence closed, and convex, and a closed
convex set is the one its support function denotes.

This is the arrow from polytopes to support functions of
[1, Fig. 1 (Polytopes → Support Functions)].

## Inputs
* `P` – vertex polytope

## Hypotheses
* none

## Conclusion
* support function equals the polytope

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

variable {α : Type} [NormedAddCommGroup α] [NormedSpace ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem VPolytope.supportFunction_exact (P : VPolytope α) :
    P.supportFunction.construct = P.construct :=
  SupportFunction.ofSet_exact P.convex_construct P.isCompact_construct.isClosed

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

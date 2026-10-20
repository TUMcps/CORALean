module

public import CORALean.ContSet.Conversion.Real.Operations.HPolytope_to_SupportFunction
public import CORALean.ContSet.HPolytope.Real.Theorems.Convex
public import CORALean.ContSet.HPolytope.Real.Theorems.IsClosed
public import CORALean.ContSet.SupportFunction.Real.Theorems.OfSetExact

@[expose] public section

/-!
# A halfspace description as a support function

Exact: a halfspace description is closed and convex, and a closed convex set is the one its support
function denotes.

This is the arrow from polytopes to support functions of
[1, Fig. 1 (Polytopes → Support Functions)].

## Inputs
* `P` – halfspace polytope

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

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.supportFunction_exact (P : HPolytope (Vec ℝ n)) :
    P.supportFunction.construct = P.construct :=
  SupportFunction.ofSet_exact P.convex_construct P.isClosed_construct

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

import CORALean.ContSet.PolyZonotope.Real.Operations.Restructure
import CORALean.ContSet.PolyZonotope.Real.Theorems.DependentExact
import CORALean.ContSet.PolyZonotope.Real.Theorems.ReduceByOuter

/-!
# `restructure` over-approximates the set

The enclosure [1, Prop. 17] states, split into where it widens and where it
does not.

Two steps, and only the first of them widens: `reduceBy_outer` boxes the
independent block, and `dependent_exact` is an equality — the fresh factors are
exactly what the coefficients they replace were.

That split is the whole content of the operation. It says where the
over-approximation comes from, and that swapping the boxing for any other
reduction leaves the second half untouched, which is why CORA can offer five
methods against one conversion.

## References

* [1] N. Kochdumper and M. Althoff. "Sparse Polynomial Zonotopes: A Novel Set
      Representation for Reachability Analysis". IEEE Transactions on Automatic
      Control, 2021.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Boxing the independent block is the only step that widens; making the box
dependent is an equality. -/
theorem PolyZonotope.restructure_outer (pZ : PolyZonotope (Vec ℝ n)) :
    pZ.construct ⊆ pZ.restructure.construct :=
  (PolyZonotope.reduceBy_outer pZ _ _).trans (PolyZonotope.dependent_exact _).subset

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

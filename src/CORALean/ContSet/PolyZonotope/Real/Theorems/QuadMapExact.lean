import CORALean.ContSet.PolyZonotope.Real.Theorems.DependentExact
import CORALean.ContSet.PolyZonotope.Real.Theorems.QuadMapDepExact

/-!
# `PolyZonotope.quadMap` is exactly the image under a quadratic map

The result is [1, Prop. 13], the general case.

The claim the representation exists for, and one no convex representation here
can make. `quadMapDep` does the work under an empty independent block, and
`dependent` is what empties it — exactly, so nothing is lost on the way in
either.

At `Zonotope.polyZonotope` — no independent generators, and already dependent —
this is the other half of [2, Thm. 1], the case [1] generalises: a zonotope's
quadratic map is exactly a polynomial zonotope.

## References

* [1] N. Kochdumper and M. Althoff. "Sparse Polynomial Zonotopes: A Novel Set
      Representation for Reachability Analysis". IEEE Transactions on Automatic
      Control, 2021.
* [2] M. Althoff. "Reachability Analysis of Nonlinear Systems using Conservative
      Polynomialization and Non-Convex Sets". HSCC 2013.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   12-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix PolyZonotope

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.quadMap_exact (Q : Fin m → Mat ℝ n n) (pZ : PolyZonotope (Vec ℝ n)) :
    quadEval Q '' pZ.construct = (pZ.quadMap Q).construct := by
  rw [pZ.dependent_exact]
  exact PolyZonotope.quadMapDep_exact Q pZ.dependent rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

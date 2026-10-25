module

public import CORALean.ContSet.PolyZonotope.Real.Theorems.DependentExact
public import CORALean.ContSet.PolyZonotope.Real.Theorems.QuadMapDepExact

@[expose] public section

/-!
# `PolyZonotope.quadMap` is exactly the image under a quadratic map

The result is [1, Prop. 13], the general case. The claim the representation exists for, and
one no convex representation here can make. `quadMapDep` does the work under an empty
independent block, and `dependent` empties it exactly, so nothing is lost on the way in. At
`Zonotope.polyZonotope` (no independent generators, already dependent) this is the other half
of [2, Thm. 1], the case [1] generalises: a zonotope's quadratic map is a polynomial zonotope.

## Inputs
* `Q` – family of quadratic form matrices
* `pZ` – polynomial zonotope

## Hypotheses
* none

## Conclusion
* the quadratic image of the set equals the result

## References

* [1] N. Kochdumper and M. Althoff. "Sparse Polynomial Zonotopes: A Novel Set
      Representation for Reachability Analysis". IEEE Transactions on Automatic
      Control, 2021.
* [2] M. Althoff. "Reachability Analysis of Nonlinear Systems using Conservative Polynomialization
      and Non-Convex Sets". Proceedings of the 16th international conference on Hybrid systems:
      computation and control, 2013.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   12-September-2026
-- Reviewed:      ---


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

module

public import CORALean.ContSet.ConPolyZono.Real.Theorems.DependentExact
public import CORALean.ContSet.ConPolyZono.Real.Theorems.QuadMapDepExact

@[expose] public section

/-!
# `ConPolyZono.quadMap` is exactly the image under a quadratic map

The result is [1, Prop. 10].

`quadMapDep` needs an empty independent block, which `hq` asks for; `quadMap`
supplies it by running `dependent` first, and `dependent` is exact. Together
with `intersection_exact` this is what a nonlinear reachability step needs: propagate
through a quadratic map, then cut by a guard, neither losing anything.

## Inputs
* `Q` – family of quadratic forms
* `cPZ` – constrained polynomial zonotope

## Hypotheses
* none

## Conclusion
* the image under the quadratic map is the result's set

## References

* [1] N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta
      Informatica, 2023.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   04-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix PolyZonotope

variable {n k : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.quadMap_exact (Q : Fin k → Mat ℝ n n) (cPZ : ConPolyZono (Vec ℝ n)) :
    quadEval Q '' cPZ.construct = (cPZ.quadMap Q).construct := by
  rw [cPZ.dependent_exact]
  exact ConPolyZono.quadMapDep_exact Q cPZ.dependent rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

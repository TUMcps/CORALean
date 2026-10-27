module

public import CORALean.ContSet.ConPolyZono.Real.Theorems.IntersectionDepExact
public import CORALean.ContSet.ConPolyZono.Real.Theorems.DependentExact

@[expose] public section

/-!
# `ConPolyZono.intersection` is exactly the intersection

The result is [1, Prop. 11].

The claim the representation exists for, and the one no convex representation
here can make without giving something away.

`intersectionDep_exact` does the work; `dependent_exact` empties
the independent blocks it asks for, and empties them costlessly.

## Inputs
* `cPZ₁` – first operand
* `cPZ₂` – second operand

## Hypotheses
* none

## Conclusion
* the intersection is the result's set

## References

* [1] [N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta Informatica,
      2023.](../../../../../../references/2023/kochdumper-constrained-polyzonotopes.md)
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.intersection_exact (cPZ₁ cPZ₂ : ConPolyZono (Vec ℝ n)) :
    cPZ₁.construct ∩ cPZ₂.construct = (cPZ₁.intersection cPZ₂).construct := by
  rw [cPZ₁.dependent_exact, cPZ₂.dependent_exact]
  exact ConPolyZono.intersectionDep_exact cPZ₁.dependent cPZ₂.dependent rfl rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

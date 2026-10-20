module

public import CORALean.ContSet.ConPolyZono.Real.Operations.IntersectionDep
public import CORALean.ContSet.ConPolyZono.Real.Operations.Dependent
public import CORALean.ContSet.Interval.Real.Operations.Point

@[expose] public section

/-!
# `ConPolyZono.intersection`

CORA's `@conPolyZono/and_`, and the reason a constrained representation exists:
two constrained polynomial zonotopes intersect to one, exactly.

`intersection` runs `intersectionDep` on the two `dependent` sets: an
independent coefficient answers to no constraint, so it could move the two
points apart with nothing in the system to forbid it. Freeing the independent
blocks into factors first is what makes this exact where CORA's `and_` encloses.

## Inputs
* `cPZ₁` – first operand
* `cPZ₂` – second operand

## Output
* intersection of the two sets
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The two `dependent` sets, their points made to agree exactly. -/
def ConPolyZono.intersection (cPZ₁ cPZ₂ : ConPolyZono (Vec ℝ n)) : ConPolyZono (Vec ℝ n) :=
  ConPolyZono.intersectionDep cPZ₁.dependent cPZ₂.dependent

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

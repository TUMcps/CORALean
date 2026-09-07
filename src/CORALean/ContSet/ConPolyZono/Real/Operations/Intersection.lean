import CORALean.ContSet.ConPolyZono.Real.Operations.IntersectionDep
import CORALean.ContSet.ConPolyZono.Real.Operations.Dependent
import CORALean.ContSet.Interval.Real.Operations.Point

/-!
# `ConPolyZono.intersection`

CORA's `@conPolyZono/and_`, and the reason a constrained representation exists:
two constrained polynomial zonotopes intersect to one, exactly.

`intersection` runs `intersectionDep` on the two `dependent` sets, at zero tolerance: an
independent coefficient answers to no constraint, so it could move the two
points apart with nothing in the system to forbid it. Freeing the independent
blocks into factors first is what makes this exact where CORA's `and_` encloses.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Zero tolerance: the two points agree exactly. -/
def ConPolyZono.intersection (cPZ₁ cPZ₂ : ConPolyZono (Vec ℝ n)) : ConPolyZono (Vec ℝ n) :=
  ConPolyZono.intersectionDep cPZ₁.dependent cPZ₂.dependent (Interval.point 0)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

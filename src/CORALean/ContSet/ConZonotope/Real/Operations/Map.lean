import CORALean.ContSet.ConZonotope.Real.ConZonotope

/-!
# `ConZonotope.map`

A linear map applies to centre and generators; the constraints are on the
coefficients and so are untouched. This is why every multiplication a
constrained zonotope carries is as exact as a zonotope's.
-/

-- Authors:       Tobias Ladner
-- Written:       01-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α β : Type} [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]


-- =====================================  MAIN DEFINITION  ====================================== --

def ConZonotope.map (f : α →ₗ[ℝ] β) (cZ : ConZonotope α) : ConZonotope β where
  h := cZ.h
  c := f cZ.c
  G := fun j => f (cZ.G j)
  P := cZ.P

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

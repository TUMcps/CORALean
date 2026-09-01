import CORALean.ContSet.ConZonotope.ConZonotope

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

namespace CORALean.Real

variable {α β : Type} [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]

def ConZonotope.map (f : α →ₗ[ℝ] β) (C : ConZonotope α) : ConZonotope β where
  h := C.h
  q := C.q
  c := f C.c
  G := fun j => f (C.G j)
  A := C.A
  b := C.b

end CORALean.Real

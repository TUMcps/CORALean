import CORALean.ContSet.PolyZonotope.Real.PolyZonotope

/-!
# `PolyZonotope.map`

A linear map applies to the centre and to both generator blocks, and touches
neither the exponent matrix nor any of the three counts: the monomials are
scalars, and a linear map commutes with scaling.

That is the whole reason a polynomial zonotope propagates through a linear layer
without loss, exactly as a zonotope does. Every multiplication this
representation carries is this at a particular map.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α β : Type} [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]


-- =====================================  MAIN DEFINITION  ====================================== --

def PolyZonotope.map (f : α →ₗ[ℝ] β) (PZ : PolyZonotope α) : PolyZonotope β where
  p := PZ.p
  h := PZ.h
  q := PZ.q
  c := f PZ.c
  G := fun i => f (PZ.G i)
  E := PZ.E
  GI := fun j => f (PZ.GI j)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

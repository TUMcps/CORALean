module

public import CORALean.ContSet.PolyZonotope.Real.PolyZonotope
public import Mathlib.Algebra.Module.LinearMap.Defs

@[expose] public section

/-!
# `PolyZonotope.map`

The construction is [1, Prop. 2.8].

A linear map applies to the centre and to both generator blocks, and touches
neither the exponent matrix nor any of the three counts: the monomials are
scalars, and a linear map commutes with scaling.

That is the whole reason a polynomial zonotope propagates through a linear layer
without loss, exactly as a zonotope does. Every multiplication this
representation carries is this at a particular map.

## References

* [1] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural
      Network Verification using Sensitivity Analysis". HSCC 2023.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α β : Type} [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]


-- =====================================  MAIN DEFINITION  ====================================== --

def PolyZonotope.map (f : α →ₗ[ℝ] β) (pZ : PolyZonotope α) : PolyZonotope β where
  p := pZ.p
  h := pZ.h
  q := pZ.q
  c := f pZ.c
  G := fun i => f (pZ.G i)
  E := pZ.E
  GI := fun j => f (pZ.GI j)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

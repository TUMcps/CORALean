module

public import CORALean.ContSet.PolyZonotope.Real.PolyZonotope
public import Mathlib.Algebra.Module.LinearMap.Defs

@[expose] public section

/-!
# `PolyZonotope.map`

The construction is [1, Prop. 2.8]. A linear map applies to the center and to both generator
blocks, and touches neither the exponent matrix nor any of the three counts: the monomials
are scalars, and a linear map commutes with scaling. That is why a polynomial zonotope
propagates through a linear layer without loss, as a zonotope does; every multiplication this
representation carries is this at a particular map.

## Inputs
* `f` – linear map
* `pZ` – polynomial zonotope

## Output
* polynomial zonotope of the image

## References

* [1] [T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural Network Verification
      using Sensitivity Analysis". Proceedings of the 26th ACM International Conference on Hybrid
      Systems: Computation and Control,
      2023.](../../../../../../references/2023/ladner-hscc-abstraction-refinement.md)
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

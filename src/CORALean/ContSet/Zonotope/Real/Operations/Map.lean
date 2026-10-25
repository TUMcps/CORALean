module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import Mathlib.Algebra.Module.LinearMap.Defs

@[expose] public section

/-!
# `Zonotope.map`

A linear map applies to center and generators alike, which is why a zonotope is
closed under one [1, Sec. 2] and the generator count is untouched.

Every multiplication a zonotope carries is this at a particular map — `mtimes`
at `A *ᵥ ·`, matrix multiplication at `A * ·` or `· * A` — so none of them needs
an exactness proof of its own.

## Inputs
* `f` – linear map
* `Z` – zonotope

## Output
* zonotope of the images under `f`

## References

* [1] A. Girard. "Reachability of Uncertain Linear Systems Using Zonotopes". Hybrid Systems:
      Computation and Control, 2005.
-/

-- Authors:       Claude Opus 5
-- Written:       01-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α β : Type} [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]


-- =====================================  MAIN DEFINITION  ====================================== --

def Zonotope.map (f : α →ₗ[ℝ] β) (Z : Zonotope α) : Zonotope β where
  h := Z.h
  c := f Z.c
  G := fun j => f (Z.G j)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

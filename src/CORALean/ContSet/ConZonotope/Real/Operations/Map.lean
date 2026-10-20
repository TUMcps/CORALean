module

public import CORALean.ContSet.ConZonotope.Real.ConZonotope

@[expose] public section

/-!
# `ConZonotope.map`

A linear map applies to center and generators [1, Prop. 1]; the constraints are on the
coefficients and so are untouched. This is why every multiplication a
constrained zonotope carries is as exact as a zonotope's.

## Inputs
* `f` – linear map
* `cZ` – constrained zonotope

## Output
* the image under the map

## References

* [1] J. K. Scott, D. M. Raimondo, G. R. Marseglia and R. D. Braatz. "Constrained zonotopes:
      A new tool for set-based estimation and fault detection". Automatica, 69:126-136,
      2016.
-/

-- Authors:       Claude Opus 5
-- Written:       01-September-2026
-- Last update:   ---
-- Reviewed:      ---


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

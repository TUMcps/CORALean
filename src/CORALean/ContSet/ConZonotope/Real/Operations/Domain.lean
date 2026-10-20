module

public import CORALean.ContSet.ConZonotope.Real.ConZonotope

@[expose] public section

/-!
# `ConZonotope.domain`

The coefficients the representation admits, as one polytope: the unit box a
zonotope ranges over, intersected with what `P` adds.

The box is kept outside `P` in the structure, so that `zonotope` is an enclosure
whatever `P` says; this is where the two are put back together, and it is what
lets a constrained zonotope be read as an affine image of a polytope.

## Inputs
* `cZ` – constrained zonotope

## Output
* the polytope of admissible coefficients
-/

-- Authors:       Claude Opus 5
-- Written:       04-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

def ConZonotope.domain (cZ : ConZonotope α) : HPolytope (Vec ℝ cZ.h) :=
  (HPolytope.unitBox cZ.h).intersection cZ.P

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

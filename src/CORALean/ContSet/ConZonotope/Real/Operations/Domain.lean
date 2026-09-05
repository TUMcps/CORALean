import CORALean.ContSet.ConZonotope.Real.ConZonotope

/-!
# `ConZonotope.domain`

The coefficients the representation admits, as one polytope: the unit box a
zonotope ranges over, intersected with what `P` adds.

The box is kept outside `P` in the structure, so that `zonotope` is an enclosure
whatever `P` says; this is where the two are put back together, and it is what
lets a constrained zonotope be read as an affine image of a polytope.
-/

-- Authors:       Tobias Ladner
-- Written:       04-September-2026
-- Last update:   05-September-2026
-- Last revision: ---

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]

def ConZonotope.domain (C : ConZonotope α) : HPolytope (Vec ℝ C.h) :=
  (HPolytope.unitBox C.h).and C.P

end CORALean.Real

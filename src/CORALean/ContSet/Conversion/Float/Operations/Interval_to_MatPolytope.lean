module

public import CORALean.ContSet.Conversion.Float.Operations.Basic
public import CORALean.ContSet.VPolytope.Float.Operations.Unvec
public import CORALean.ContSet.Interval.Float.Operations.Vec

@[expose] public section

/-!
# An interval matrix as its corners, over a floating-point scalar

CORA's `matPolytope(intMat)`: the vertices of the interval matrix, which are the vertices of the
stacked interval (`reshape(interval(intMat), [], 1)`) reshaped back into matrices. The float
version stacks the bounds, takes the corners of the stacked box and unstacks them.

## Inputs
* `I` – interval matrix

## Output
* matrix polytope of the corner matrices
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {m n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The corners of the stacked box, unstacked. -/
def Interval.matPolytope (I : Interval (Mat 𝕋 m n)) : VPolytope (Mat 𝕋 m n) :=
  (Interval.vPolytope I.vec).unvec

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

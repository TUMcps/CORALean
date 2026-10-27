module

public import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_VPolytope
public import CORALean.ContSet.VPolytope.Float.Operations.Unvec
public import CORALean.ContSet.Zonotope.Float.Operations.Vec

@[expose] public section

/-!
# A matrix zonotope as its corners, over a floating-point scalar

CORA's `matPolytope(matZ)`: the vertices of the stacked zonotope `zonotope(matZ)` reshaped back
into matrices. The float version stacks the zonotope, takes its rounded corners with the rounding
gap in the error box, and unstacks them.

## Inputs
* `Z` – matrix zonotope

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

/-- The corners of the stacked zonotope, unstacked. -/
def Zonotope.matPolytope (Z : Zonotope (Mat 𝕋 m n)) : VPolytope (Mat 𝕋 m n) :=
  Z.vec.vPolytope.unvec

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

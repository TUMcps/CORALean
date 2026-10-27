module

public import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Interval.Float.Operations.MatNorm

@[expose] public section

/-!
# `Zonotope.matNorm`, over a floating-point scalar

CORA's `norm` of a matrix zonotope, which is `norm(intervalMatrix(matZ), type)`: the enclosing box
of the zonotope (`matInterval`, as CORA's `intervalMatrix`) and then the norm of that box,
`Interval.matNorm`, rounded up. CORA's help text calls the result an approximate maximum norm.

## Inputs
* `steps` – number of Newton steps of the square root
* `p` – norm type
* `Z` – matrix zonotope

## Output
* upper bound of the norm of every member
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

/-- The norm of `type` of the enclosing box. -/
def Zonotope.matNorm (steps : ℕ) (p : Real.Interval.NormType) (Z : Zonotope (Mat 𝕋 m n)) : 𝕋 :=
  Interval.matNorm steps p Z.matInterval

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

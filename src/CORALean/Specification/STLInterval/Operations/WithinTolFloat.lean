module

public import CORALean.Global.Float.Interfaces

@[expose] public section

/-!
# `withinTol` of two bounds over a float scalar

`withinTol(a,b,tol)` of two bounds that are stored values or `inf`, decided exactly on the reals
they denote (`ExactLe.withinTol`): two stored values as MATLAB's test, `inf` only with `inf`. What
it decides is `IsWithinTol` of the bounds read as extended reals (`withinTolFloat_iff`).

## Inputs
* `tol` – tolerance

## Output
* whether the bounds agree up to the tolerance
-/

-- Authors:       Claude Opus 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ExactLe 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `withinTol(a,b,tol)` of two bounds, `inf` agreeing only with `inf`. -/
def STLInterval.withinTolFloat (tol : 𝕋) : WithTop 𝕋 → WithTop 𝕋 → Bool
  | some a, some b => ExactLe.withinTol tol a b
  | none, none => true
  | _, _ => false

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

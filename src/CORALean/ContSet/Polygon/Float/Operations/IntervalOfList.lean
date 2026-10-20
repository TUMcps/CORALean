module

public import CORALean.ContSet.Polygon.Float.Polygon
public import CORALean.ContSet.Conversion.Float.Operations.Basic
public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.Basic

@[expose] public section

/-!
# `Polygon.intervalOfList`, over a floating-point scalar

The hull of a list of pieces' boxes (`Interval.or`), the empty box for none.

## Inputs
* none

## Output
* the hull of a list of pieces' boxes
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The hull of a list of pieces' boxes. -/
def Polygon.intervalOfList : List (VPolytope (Vec 𝕋 2)) → Interval (Vec 𝕋 2)
  | [] => Interval.empty 2
  | [p] => VPolytope.interval p
  | p :: q :: ps => (VPolytope.interval p).or (Polygon.intervalOfList (q :: ps))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

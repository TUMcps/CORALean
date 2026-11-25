module

public import CORALean.ContSet.ConZonotope.Float.Operations.SplitWith
public import CORALean.ContSet.Conversion.Float.Operations.Basic
public import CORALean.ContSet.Interval.Float.Operations.SplitAt
public import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_ConZonotope
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval

@[expose] public section

/-!
# `ConZonotope.split`, over a floating-point scalar

The set intersected with the two halves of its bounding box along dimension `d`, as over ℝ:
the box is `ConZonotope.interval`, cut by `Interval.splitAt`, each half converted by
`Interval.conZonotope` and intersected with the set by the float `intersection`
(`ConZonotope.splitWith` at that box).

## Inputs
* `cZ` – float constrained zonotope
* `d` – dimension to cut along

## Output
* the two halves of the set
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ConZonotope.split (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) (d : Fin n) :
    ConZonotope 𝕋 (Vec 𝕋 n) × ConZonotope 𝕋 (Vec 𝕋 n) :=
  -- the bounding box of the set
  let I := cZ.interval
  -- the box cut at the middle of side `d`, the set intersected with each half
  cZ.splitWith I d

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

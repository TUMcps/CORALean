module

public import CORALean.ContSet.Conversion.Float.Operations.Basic
public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.HPolytope_to_VPolytope
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_VPolytope

@[expose] public section

/-!
# `VPolytope.intersection`, over a floating-point scalar

Through boxes, as in the exact layer: the intersection's vertices are generally none of either
operand's. Each operand's box already absorbed its error box, intersecting boxes is exact, and the
corners are stored bounds copied, so this operation rounds nowhere. The `Intersection` class carries
no direction family, and vertices are not computable soundly at float: enumeration would need a
solver or a proof of its rounding (CORA stays in halfspaces and stacks the rows). So the result is a
box, `box P₁ ∩ box P₂`, an enclosure that can be far from the intersection (two thin diagonal strips
give the strips' whole bounding box). Where the caller can name directions,
`VPolytope.intersectionCut` cuts the same box to both operands' halfspaces.

## Inputs
* `P₁` – first polytope
* `P₂` – second polytope

## Output
* box polytope of the intersection of the operands' boxes
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      14-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def VPolytope.intersection (P₁ P₂ : VPolytope (Vec 𝕋 n)) : VPolytope (Vec 𝕋 n) :=
  Interval.vPolytope (P₁.interval.intersection P₂.interval)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.ContSet.Conversion.Float.Operations.Basic
public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.HPolytope_to_VPolytope
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_VPolytope

@[expose] public section

/-!
# `VPolytope.intersection`, over a floating-point scalar

Through boxes, as in the exact layer, and for the same reason: the
intersection's vertices are generally none of either operand's. Each operand's
box already absorbed its error box, intersecting boxes is exact, and the corners
are stored bounds copied — so this operation rounds nowhere, all of its
imprecision being in the detour rather than in the arithmetic.

Why this and not more. The `Intersection` class carries no direction family, and the
intersection's vertices are not computable soundly at float: a vertex enumeration of the
halfspace description would need either a solver or a proof of its rounding, neither of
which exists here (CORA itself stays in halfspaces and stacks the rows; a vertex set is
never recomputed). So the result is a box, `box P₁ ∩ box P₂`: an enclosure that can be far
from the intersection (two thin diagonal strips meeting in a small square give the
strips' whole bounding box). Where the caller can name directions,
`VPolytope.intersectionCut` is tighter: the same box cut to both operands' halfspaces. A
result that is not a box needs a sound vertex enumeration at float, which is not here.
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

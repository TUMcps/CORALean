module

public import CORALean.ContSet.Polygon.Float.Polygon
public import CORALean.ContSet.VPolytope.Float.Operations.Intersection

@[expose] public section

/-!
# `Polygon.and`, over a floating-point scalar

CORA's `@polygon/and_` read at the region, as over ℝ: every pair of pieces intersected. The
real layer intersects a pair at given directions; here a pair is intersected by the float
`VPolytope.intersection`, the box hulls of the two pieces intersected, which is coarser and
outer.

## Inputs
* `P` – polygon
* `Q` – polygon

## Output
* all pairs of pieces, intersected
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- All pairs of pieces, intersected. -/
def Polygon.and (P Q : Polygon 𝕋) : Polygon 𝕋 :=
  ⟨(P.sets.product Q.sets).map fun pq => VPolytope.intersection pq.1 pq.2⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

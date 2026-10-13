module

public import CORALean.ContSet.Polygon.Real.Operations.Plus
public import CORALean.ContSet.ContSet.Operations.Minus
public import CORALean.ContSet.SetUnion.Instances

@[expose] public section

/-!
# `Polygon.minus`

CORA's `@polygon/minus` for a numeric subtrahend: `pgon + (-p)`, which is `ContSet.minus` at the
polygon, the point entering as a union of one singleton (`OfPoint (SetUnion S)`). CORA throws
for a polygon subtrahend (`minkDiff` is the Minkowski difference), so that case is not defined
here either.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

def Polygon.minus (P : Polygon) (p : Vec ℝ 2) : Polygon := ContSet.minus P p

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

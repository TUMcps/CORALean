module

public import CORALean.ContSet.Polygon.Real.Operations.Subtract
public import CORALean.ContSet.Polygon.Real.Operations.Center
public import CORALean.ContSet.Polygon.Real.Operations.Minus
public import CORALean.ContSet.Polygon.Real.Operations.Times
public import CORALean.ContSet.Polygon.Real.Operations.LinComb
public import CORALean.ContSet.Polygon.Real.Operations.Plus
public import CORALean.ContSet.SetUnion.Instances

@[expose] public section

/-!
# `Polygon.minkDiff`

CORA's `polygon/minkDiff(pgon, subtrahend)` for a polygon subtrahend. Both operands are moved by
the center `c` of the subtrahend, the subtrahend is mirrored, and its translates are swept along
the boundary of the minuend: for each edge `(Vi, Vi1)` of `vertices_(pgon)`, the
`linComb` of the mirrored subtrahend shifted to `Vi` and to `Vi1`. The region swept is cut out of
the minuend with `subtract`. The boundary vertex loop `V` of the shifted minuend is the argument
(a `polyshape` boundary, R-PG); the loop closes from the last vertex to the first, and the
`NaN` separators of several regions and holes are not modelled. The result is the region,
`Polygon.subtract`'s, not a polygon.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The minuend with the swept region of the mirrored subtrahend cut out. -/
noncomputable def Polygon.minkDiff (A B : Polygon) (V : List (Vec ℝ 2)) : Set (Vec ℝ 2) :=
  -- `c = center(subtrahend)`, `subtrahend = subtrahend - c` and `pgon = pgon - c`
  let c : Vec ℝ 2 := B.center
  let B₀ : Polygon := B.minus c
  let A₀ : Polygon := A.minus c
  -- `subtrahend = -subtrahend`
  let Bm : Polygon := Polygon.times (-1) B₀
  -- `linComb(subtrahend+Vi, subtrahend+Vi1)` for every edge, united into `diff`
  let edge : Vec ℝ 2 × Vec ℝ 2 → Polygon := fun e =>
    Polygon.linComb (Polygon.plus Bm (OfPoint.ofPoint e.1)) (Polygon.plus Bm (OfPoint.ofPoint e.2))
  let diff : Polygon := ⟨(V.zip (V.rotate 1)).flatMap fun e => (edge e).sets⟩
  -- `pgon.set = subtract(pgon.set, diff.set)`
  Polygon.subtract A₀ diff

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

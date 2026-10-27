module

public import CORALean.ContSet.ConZonotope.Float.ConZonotope
public import CORALean.ContSet.HPolytope.Float.Operations.RescaleCols
public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.Zonotope.Float.Operations.Basic

@[expose] public section

/-!
# `ConZonotope.rescale` over a floating-point scalar

CORA's `conZonotope/rescale` and [1, Prop. 4]'s eq. 24 on the stored floats: the coefficient box
`[ξL, ξU]` is mapped back onto `[-1, 1]` by `ξ = ξm + diag(ξr) δ`, with `ξm` the rounded midpoint
and `ξr` a radius rounded up from it to both ends. The new center `c + G ξm` and generators
`G diag(ξr)` are rounded down, what that costs going into the error box (the center's as a residual,
the generators' as a generator error against `|δ| ≤ 1`, the gap `mulDown_gap` bounds). The
constraint is `HPolytope.rescaleCols`, the same substitution in its rows, every rounding written
into the rows' slacks so an equality stays an equality and every rescaled coefficient vector stays
feasible. The interval is an argument, as over ℝ; the result is outer, never the exact rescaling.

## Inputs
* `cZ` – float constrained zonotope
* `ξL` – lower coefficient bounds
* `ξU` – upper coefficient bounds

## Output
* enclosure with the coefficient box mapped onto the unit box

## References

* [1] [J. K. Scott, D. M. Raimondo, G. R. Marseglia and R. D. Braatz. "Constrained zonotopes: A new
      tool for set-based estimation and fault detection". Automatica,
      2016.](../../../../../../references/2016/scott-automatica-constrained-zonotopes.md)
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       04-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Prop. 4]: `{G diag(ξr), c + G ξm, A diag(ξr), b − A ξm}`, every rounding paid outward. -/
def ConZonotope.rescale (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) (ξL ξU : Vec 𝕋 cZ.h) : ConZonotope
    𝕋 (Vec 𝕋 n) :=
  let ξm : Vec 𝕋 cZ.h := fun j => half (addDown (ξU j) (ξL j))      -- ξm ≈ ½(ξU + ξL)
  let ξr : Vec 𝕋 cZ.h := fun j =>                                    -- ξr covers both ends
    maximum (subUp (ξU j) (ξm j)) (subUp (ξm j) (ξL j))
  -- c + G ξm, rounded down and up
  let cLo : Vec 𝕋 n := fun i => addDown (cZ.c i) (dotDown (fun j => cZ.G j i) ξm)
  let cHi : Vec 𝕋 n := fun i => addUp (cZ.c i) (dotUp (fun j => cZ.G j i) ξm)
  -- how far each entry of `G diag(ξr)`, rounded down, may be off
  let gapG : Mat 𝕋 n cZ.h := fun i j =>
    subUp (mulUp (cZ.G j i) (ξr j)) (mulDown (cZ.G j i) (ξr j))
  { h := cZ.h
    c := cLo
    G := fun j i => mulDown (cZ.G j i) (ξr j)
    P := cZ.P.rescaleCols ξm ξr
    I_error := (cZ.I_error.plus (Interval.residual cLo cHi cLo)).plus
        (Zonotope.generatorError gapG) }

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

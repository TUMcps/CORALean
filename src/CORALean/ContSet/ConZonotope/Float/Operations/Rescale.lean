import CORALean.ContSet.ConZonotope.Float.ConZonotope
import CORALean.ContSet.Interval.Float.Operations.Plus
import CORALean.ContSet.Interval.Float.Operations.Residual
import CORALean.ContSet.Zonotope.Float.Operations.GeneratorError

/-!
# `ConZonotope.rescale` over a floating-point scalar

CORA's `conZonotope/rescale` and [1, Prop. 4]'s eq. 24 on the stored floats: the coefficient
box `[ξL, ξU]` is mapped back onto `[-1, 1]` by `ξ = ξm + diag(ξr) δ`. Here `ξm` is the
rounded midpoint and `ξr` a radius rounded up from it to both ends, so the box around `ξm`
covers `[ξL, ξU]` whatever the rounding did. The new centre `c + G ξm` and generators
`G diag(ξr)` are rounded down, what that costs going into the error box (the centre's as a
residual, the generators' as a generator error against `|δ| ≤ 1`); the constraint rows
`A diag(ξr)` are rounded down too, their right-hand sides `b − A ξm` rounded outward and
widened by the same generator error, so every rescaled coefficient vector stays feasible. The
interval is an argument, as over ℝ; the result is outer, never the exact rescaling.

## References

* [1] J. K. Scott, D. M. Raimondo, G. R. Marseglia and R. D. Braatz. "Constrained zonotopes:
      A new tool for set-based estimation and fault detection". Automatica, 69:126-136,
      2016.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
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
  -- how far each entry of `M diag(ξr)`, rounded down, may be off
  let gapG : Mat 𝕋 n cZ.h := fun i j =>
    subUp (mulUp (cZ.G j i) (ξr j)) (mulDown (cZ.G j i) (ξr j))
  let gapA : Mat 𝕋 cZ.P.m cZ.h := fun k j =>
    subUp (mulUp (cZ.P.A k j) (ξr j)) (mulDown (cZ.P.A k j) (ξr j))
  let gapAe : Mat 𝕋 cZ.P.me cZ.h := fun k j =>
    subUp (mulUp (cZ.P.Ae k j) (ξr j)) (mulDown (cZ.P.Ae k j) (ξr j))
  { h := cZ.h
    c := cLo
    G := fun j i => mulDown (cZ.G j i) (ξr j)
    P :=
      { m := cZ.P.m
        A := fun k j => mulDown (cZ.P.A k j) (ξr j)
        b := fun k => addUp (subUp (cZ.P.b k) (dotDown (cZ.P.A k) ξm)) (sumUp (gapA k))
        me := cZ.P.me
        Ae := fun k j => mulDown (cZ.P.Ae k j) (ξr j)
        be := ⟨fun k => subDown (subDown (cZ.P.be.inf k) (dotUp (cZ.P.Ae k) ξm)) (sumUp (gapAe k)),
               fun k => addUp (subUp (cZ.P.be.sup k) (dotDown (cZ.P.Ae k) ξm)) (sumUp (gapAe k))⟩ }
    E := (cZ.E.plus (Interval.residual cLo cHi cLo)).plus (Zonotope.generatorError gapG) }

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

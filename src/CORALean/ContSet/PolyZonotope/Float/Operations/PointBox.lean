import CORALean.ContSet.Interval.Float.Operations.Mtimes
import CORALean.ContSet.Interval.Float.Operations.Plus
import CORALean.ContSet.Interval.Float.Operations.Point
import CORALean.ContSet.PolyZonotope.Float.Operations.MonoBox
import CORALean.ContSet.PolyZonotope.Float.PolyZonotope

/-!
# `PolyZonotope.pointBox`

The interval evaluation of the dependent point map `α ↦ c + Σₗ Gₗ αᴱˡ` over a box of factor
values: CORA's `aux_funcPoly` of `@polyZonotope/innerApprox` (`val = c + Σ G(:,i)·prod(x.^E(:,i))`)
called on an interval, which is how `innerApproxImage` encloses `f(X_)` and `f(center(X_))`.
The monomials come from `monoBox`, the stored generators multiply them by `Interval.mtimes`, the
centre is added by `Interval.plus`. The independent generators and the error box are not part of
the map.
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- An interval holding the dependent point at every factor vector of the box `X`. -/
def PolyZonotope.pointBox (pZ : PolyZonotope (Vec 𝕋 n)) (X : Interval (Vec 𝕋 pZ.p)) :
    Interval (Vec 𝕋 n) :=
  -- `G` with one row per coordinate, the generators as columns
  let Gm : Mat 𝕋 n pZ.h := fun i l => pZ.G l i
  ((Interval.point pZ.c).plus (Interval.mtimes Gm (PolyZonotope.monoBox pZ.E X))).materialise

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

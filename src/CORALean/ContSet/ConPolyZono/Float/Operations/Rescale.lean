import CORALean.ContSet.ConPolyZono.Float.Operations.RescaleStep
import CORALean.ContSet.ConPolyZono.Float.Operations.UnitBox

/-!
# `ConPolyZono.rescale` over a floating-point scalar

CORA's `@conPolyZono/rescale` on the stored floats: contract the factor box `[-1,1]ᵖ` against
the constraint with `contractPoly`, and re-parametrize every factor onto the contracted box by
the float `getSubset`, factors `0, …, p-1` in turn, as over ℝ. The contractor is a parameter,
as over ℝ, here on float boxes. The midpoint of each contracted interval is rounded and the
radius rounded up from it to both ends, so `cen ± rad` covers the interval whatever the
rounding did; each `getSubset` step pays its own rounding into the error box and `b`. The
result is outer, never the exact rescaling.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `contract` is CORA's `contractPoly` at the constraint `A μ(α) = b`. -/
def ConPolyZono.rescale (cPZ : ConPolyZono 𝕋 n)
    (contract : Interval (Vec 𝕋 cPZ.p) → Interval (Vec 𝕋 cPZ.p)) : ConPolyZono 𝕋 n :=
  let dom := ConPolyZono.unitBox 𝕋 cPZ.p
  -- `if ~isempty(cPZ.A)`
  let dom' := if cPZ.m = 0 ∨ cPZ.s = 0 then dom else contract dom
  -- the midpoint rounded, the radius rounded up from it to both ends
  let cen : ℕ → 𝕋 := fun r =>
    if h : r < cPZ.p then half (addDown (dom'.sup ⟨r, h⟩) (dom'.inf ⟨r, h⟩)) else zero
  let rad : ℕ → 𝕋 := fun r =>
    if h : r < cPZ.p then
      maximum (subUp (dom'.sup ⟨r, h⟩) (cen r)) (subUp (cen r) (dom'.inf ⟨r, h⟩))
    else zero
  (List.range cPZ.p).foldl (ConPolyZono.rescaleStep cen rad) cPZ

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

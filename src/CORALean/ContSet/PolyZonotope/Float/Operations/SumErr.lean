module

public import CORALean.ContSet.PolyZonotope.Float.Operations.CenterResidual
public import CORALean.ContSet.Interval.Float.Operations.Plus
public import CORALean.ContSet.Interval.Float.Operations.Residual
public import CORALean.ContSet.Interval.Float.Operations.Origin
public import CORALean.ContSet.PolyZonotope.Real.Operations.Sum

@[expose] public section

/-!
# `PolyZonotope.sumErr`, over a floating-point scalar

The sum of `m` error boxes by `Interval.plus`, the error box of `PolyZonotope.sum`.
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

/-- The sum of `m` error boxes, by `Interval.plus`. -/
def PolyZonotope.sumErr : (m : ℕ) → (Fin m → Interval (Vec 𝕋 n)) → Interval (Vec 𝕋 n)
  | 0, _ => Interval.origin n
  | m + 1, f => (f 0).plus (PolyZonotope.sumErr m fun i => f i.succ)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

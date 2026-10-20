module

public import CORALean.ContSet.Taylm.Float.Operations.PowBounds
public import CORALean.ContSet.Interval.Float.Operations.MulLo
public import CORALean.ContSet.Interval.Float.Operations.MulHi

@[expose] public section

/-!
# `Taylm.prodBounds`, over a floating-point scalar

The range of a product of factors each known to lie in an interval: the corner products of the
running interval with the next factor's, rounded outward (`Interval.mulLo`, `Interval.mulHi`).

## Inputs
* none

## Output
* product of the listed intervals
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.prodBounds : {m : ℕ} → (Fin m → Interval 𝕋) → Interval 𝕋
  | 0, _ => ⟨one, one⟩
  | _ + 1, f =>
    let rest := Taylm.prodBounds fun i => f i.succ
    ⟨Interval.mulLo (f 0).inf (f 0).sup rest.inf rest.sup, Interval.mulHi (f 0).inf (f 0).sup
        rest.inf rest.sup⟩
end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
